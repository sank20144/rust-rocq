use std::collections::BTreeMap;

use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};

use crate::term::{self, Term};
use crate::translator::Translator;
use crate::types;

impl<'tcx> Translator<'tcx> {
    pub fn body(&self, def_id: DefId, name: &str, body: &mir::Body<'tcx>, borrowck: Term) -> Term {
        self.set_file(self.span_file(body.span));
        let names = debug_names(body);

        let locals: Vec<Term> = body
            .local_decls
            .iter_enumerated()
            .map(|(local, decl)| {
                let label = match names.get(&local) {
                    Some(n) => format!("_{} {n}", local.as_u32()),
                    None => format!("_{}", local.as_u32()),
                };
                term::note(
                    &label,
                    term::app(
                        "LocalDecl",
                        vec![
                            self.ty(decl.ty),
                            types::mutability(decl.mutability),
                            term::option(names.get(&local).map(|n| term::string(n))),
                            self.span(decl.source_info.span),
                        ],
                    ),
                )
            })
            .collect();

        let blocks: Vec<Term> = body
            .basic_blocks
            .iter_enumerated()
            .map(|(block, data)| {
                let label = if data.is_cleanup {
                    format!("bb{} (cleanup)", block.as_u32())
                } else {
                    format!("bb{}", block.as_u32())
                };
                term::note(
                    &label,
                    term::app(
                        "BasicBlock",
                        vec![
                            term::nat(block.as_u32() as u64),
                            term::list(data.statements.iter().map(|s| self.statement(s)).collect()),
                            match &data.terminator {
                                Some(t) => self.terminator(t),
                                None => term::app(
                                    "Term",
                                    vec![term::atom("NoSpan"), term::atom("TUnreachable")],
                                ),
                            },
                            term::boolean(data.is_cleanup),
                        ],
                    ),
                )
            })
            .collect();

        term::app(
            "Body",
            vec![
                term::note("name", term::string(name)),
                term::note("file", term::string(&self.file())),
                term::note("span", self.span(body.span)),
                term::note("generics", self.generics(def_id)),
                term::note("bounds", self.bounds(def_id)),
                term::note("args", term::nat(body.arg_count as u64)),
                term::note("locals", term::list(locals)),
                term::note("blocks", term::list(blocks)),
                term::note(
                    "regions",
                    term::list(self.take_regions().into_iter().map(term::nat).collect()),
                ),
                term::note("borrowck annotations", borrowck),
            ],
        )
    }

    pub fn generics(&self, def_id: DefId) -> Term {
        let generics = self.tcx.generics_of(def_id);
        term::list(
            generics
                .own_params
                .iter()
                .map(|p| {
                    let index = term::nat(p.index as u64);
                    let name = term::string(p.name.as_str());
                    match p.kind {
                        ty::GenericParamDefKind::Lifetime => {
                            term::app("GpLifetime", vec![index, name])
                        }
                        ty::GenericParamDefKind::Type { .. } => {
                            term::app("GpTy", vec![index, name])
                        }
                        ty::GenericParamDefKind::Const { .. } => term::app(
                            "GpConst",
                            vec![
                                index,
                                name,
                                self.ty(self.tcx.type_of(p.def_id).skip_binder()),
                            ],
                        ),
                    }
                })
                .collect(),
        )
    }

    pub fn bounds(&self, def_id: DefId) -> Term {
        term::list(
            self.tcx
                .predicates_of(def_id)
                .predicates
                .iter()
                .map(|(clause, _)| self.clause(*clause))
                .collect(),
        )
    }

    fn clause(&self, clause: ty::Clause<'tcx>) -> Term {
        match clause.kind().skip_binder() {
            ty::ClauseKind::Trait(t) => term::app(
                "BdTrait",
                vec![self.path(t.def_id()), self.generic_args(t.trait_ref.args)],
            ),
            ty::ClauseKind::Projection(p) => term::app(
                "BdProjection",
                vec![
                    self.path(p.projection_term.def_id()),
                    self.generic_args(p.projection_term.args),
                    match p.term.kind() {
                        ty::TermKind::Ty(t) => self.ty(t),
                        ty::TermKind::Const(c) => {
                            term::app("TError", vec![term::string(&self.type_const(c).render())])
                        }
                    },
                ],
            ),
            ty::ClauseKind::RegionOutlives(o) => {
                term::app("BdOutlives", vec![self.region(o.0), self.region(o.1)])
            }
            ty::ClauseKind::TypeOutlives(o) => {
                term::app("BdTyOutlives", vec![self.ty(o.0), self.region(o.1)])
            }
            ty::ClauseKind::ConstArgHasType(c, t) => {
                term::app("BdConstArgHasType", vec![self.type_const(c), self.ty(t)])
            }
            ty::ClauseKind::WellFormed(term) => match term.kind() {
                ty::TermKind::Ty(t) => term::app("BdWellFormedTy", vec![self.ty(t)]),
                ty::TermKind::Const(c) => term::app("BdWellFormedConst", vec![self.type_const(c)]),
            },
            ty::ClauseKind::ConstEvaluatable(c) => {
                term::app("BdConstEvaluatable", vec![self.type_const(c)])
            }
            ty::ClauseKind::HostEffect(h) => term::app(
                "BdHostEffect",
                vec![
                    self.path(h.trait_ref.def_id),
                    self.generic_args(h.trait_ref.args),
                    term::string(&format!("{:?}", h.constness)),
                ],
            ),
            ty::ClauseKind::UnstableFeature(sym) => {
                term::app("BdUnstableFeature", vec![term::string(sym.as_str())])
            }
        }
    }

    fn place(&self, p: &mir::Place<'tcx>) -> Term {
        term::app(
            "Place",
            vec![
                term::nat(p.local.as_u32() as u64),
                term::list(
                    p.projection
                        .iter()
                        .map(|e| self.projection_element(e))
                        .collect(),
                ),
            ],
        )
    }

    fn projection_element(&self, e: mir::PlaceElem<'tcx>) -> Term {
        use mir::ProjectionElem::*;
        match e {
            Deref => term::atom("PDeref"),
            Field(index, t) => {
                term::app("PField", vec![term::nat(index.as_u32() as u64), self.ty(t)])
            }
            Index(l) => term::app("PIndex", vec![term::nat(l.as_u32() as u64)]),
            ConstantIndex {
                offset,
                min_length,
                from_end,
            } => term::app(
                "PConstantIndex",
                vec![
                    term::nat(offset),
                    term::nat(min_length),
                    term::boolean(from_end),
                ],
            ),
            Subslice { from, to, from_end } => term::app(
                "PSubslice",
                vec![term::nat(from), term::nat(to), term::boolean(from_end)],
            ),
            Downcast(name, v) => term::app(
                "PDowncast",
                vec![
                    term::option(name.map(|s| term::string(s.as_str()))),
                    term::nat(v.as_u32() as u64),
                ],
            ),
            OpaqueCast(t) => term::app("POpaqueCast", vec![self.ty(t)]),
            UnwrapUnsafeBinder(t) => term::app("PUnwrapUnsafeBinder", vec![self.ty(t)]),
        }
    }

    fn operand(&self, o: &mir::Operand<'tcx>) -> Term {
        match o {
            mir::Operand::Copy(p) => term::app("OCopy", vec![self.place(p)]),
            mir::Operand::Move(p) => term::app("OMove", vec![self.place(p)]),
            mir::Operand::Constant(c) => term::app("OConst", vec![self.const_operand(c)]),
            mir::Operand::RuntimeChecks(c) => term::app(
                "ORuntimeCheck",
                vec![term::atom(match c {
                    mir::RuntimeChecks::UbChecks => "RcUbChecks",
                    mir::RuntimeChecks::ContractChecks => "RcContractChecks",
                    mir::RuntimeChecks::OverflowChecks => "RcOverflowChecks",
                })],
            ),
        }
    }

    fn const_operand(&self, c: &mir::ConstOperand<'tcx>) -> Term {
        term::app("ConstOp", vec![self.span(c.span), self.constant(c.const_)])
    }

    fn constant(&self, c: mir::Const<'tcx>) -> Term {
        match c {
            mir::Const::Ty(t, k) => term::app("KTy", vec![self.ty(t), self.type_const(k)]),
            mir::Const::Unevaluated(u, t) => term::app(
                "KUnevaluated",
                vec![
                    self.path(u.def),
                    self.generic_args(u.args),
                    term::option(u.promoted.map(|p| term::nat(p.as_u32() as u64))),
                    self.ty(t),
                ],
            ),
            mir::Const::Val(v, t) => term::app("KVal", vec![const_value(v), self.ty(t)]),
        }
    }

    fn rvalue(&self, r: &mir::Rvalue<'tcx>) -> Term {
        use mir::Rvalue::*;
        match r {
            Use(o, retag) => term::app(
                "RUse",
                vec![
                    self.operand(o),
                    term::atom(match retag {
                        mir::WithRetag::Yes => "RetagYes",
                        mir::WithRetag::No => "RetagNo",
                    }),
                ],
            ),
            Repeat(o, n) => term::app("RRepeat", vec![self.operand(o), self.type_const(*n)]),
            Ref(r, borrow, p) => term::app(
                "RRef",
                vec![self.region(*r), borrow_kind(*borrow), self.place(p)],
            ),
            ThreadLocalRef(def_id) => term::app("RThreadLocalRef", vec![self.path(*def_id)]),
            RawPtr(k, p) => term::app("RRawPtr", vec![raw_ptr_kind(*k), self.place(p)]),
            Cast(k, o, t) => term::app("RCast", vec![cast_kind(*k), self.operand(o), self.ty(*t)]),
            BinaryOp(op, args) => term::app(
                "RBinaryOp",
                vec![binary_op(*op), self.operand(&args.0), self.operand(&args.1)],
            ),
            UnaryOp(op, o) => term::app("RUnaryOp", vec![unary_op(*op), self.operand(o)]),
            Discriminant(p) => term::app("RDiscriminant", vec![self.place(p)]),
            Aggregate(k, fields) => term::app(
                "RAggregate",
                vec![
                    self.aggregate_kind(k),
                    term::list(fields.iter().map(|o| self.operand(o)).collect()),
                ],
            ),
            CopyForDeref(p) => term::app("RCopyForDeref", vec![self.place(p)]),
            WrapUnsafeBinder(o, t) => {
                term::app("RWrapUnsafeBinder", vec![self.operand(o), self.ty(*t)])
            }
            Reborrow(t, m, p) => term::app(
                "RReborrow",
                vec![self.ty(*t), types::mutability(*m), self.place(p)],
            ),
        }
    }

    fn aggregate_kind(&self, k: &mir::AggregateKind<'tcx>) -> Term {
        use mir::AggregateKind::*;
        match k {
            Array(t) => term::app("AgArray", vec![self.ty(*t)]),
            Tuple => term::atom("AgTuple"),
            Adt(def_id, v, args, _user_ty, active) => term::app(
                "AgAdt",
                vec![
                    self.path(*def_id),
                    term::nat(v.as_u32() as u64),
                    self.generic_args(args),
                    term::option(active.map(|f| term::nat(f.as_u32() as u64))),
                ],
            ),
            Closure(def_id, args) => term::app(
                "AgClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            Coroutine(def_id, args) => term::app(
                "AgCoroutine",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            CoroutineClosure(def_id, args) => term::app(
                "AgCoroutineClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            RawPtr(t, m) => term::app("AgRawPtr", vec![self.ty(*t), types::mutability(*m)]),
        }
    }

    fn statement(&self, s: &mir::Statement<'tcx>) -> Term {
        term::app(
            "Stmt",
            vec![self.span(s.source_info.span), self.statement_kind(&s.kind)],
        )
    }

    fn statement_kind(&self, k: &mir::StatementKind<'tcx>) -> Term {
        use mir::StatementKind::*;
        match k {
            Assign(b) => term::app("SAssign", vec![self.place(&b.0), self.rvalue(&b.1)]),
            FakeRead(b) => term::app("SFakeRead", vec![fake_read_cause(&b.0), self.place(&b.1)]),
            SetDiscriminant {
                place,
                variant_index,
            } => term::app(
                "SSetDiscriminant",
                vec![self.place(place), term::nat(variant_index.as_u32() as u64)],
            ),
            StorageLive(l) => term::app("SStorageLive", vec![term::nat(l.as_u32() as u64)]),
            StorageDead(l) => term::app("SStorageDead", vec![term::nat(l.as_u32() as u64)]),
            PlaceMention(p) => term::app("SPlaceMention", vec![self.place(p)]),
            AscribeUserType(b, kind) => term::app(
                "SAscribeUserType",
                vec![
                    self.place(&b.0),
                    term::string(&format!("{:?}", b.1)),
                    variance(*kind),
                ],
            ),
            Coverage(kind) => term::app("SCoverage", vec![term::string(&format!("{kind:?}"))]),
            Intrinsic(i) => term::app("SIntrinsic", vec![self.non_diverging_intrinsic(i)]),
            ConstEvalCounter => term::atom("SConstEvalCounter"),
            Nop => term::atom("SNop"),
            BackwardIncompatibleDropHint { place, reason } => term::app(
                "SBackwardIncompatibleDropHint",
                vec![self.place(place), term::string(&format!("{reason:?}"))],
            ),
        }
    }

    fn non_diverging_intrinsic(&self, i: &mir::NonDivergingIntrinsic<'tcx>) -> Term {
        match i {
            mir::NonDivergingIntrinsic::Assume(o) => term::app("NiAssume", vec![self.operand(o)]),
            mir::NonDivergingIntrinsic::CopyNonOverlapping(c) => term::app(
                "NiCopyNonOverlapping",
                vec![
                    self.operand(&c.src),
                    self.operand(&c.dst),
                    self.operand(&c.count),
                ],
            ),
        }
    }

    fn terminator(&self, t: &mir::Terminator<'tcx>) -> Term {
        term::app(
            "Term",
            vec![self.span(t.source_info.span), self.terminator_kind(&t.kind)],
        )
    }

    fn terminator_kind(&self, k: &mir::TerminatorKind<'tcx>) -> Term {
        use mir::TerminatorKind::*;
        match k {
            Goto { target } => term::app("TGoto", vec![basic_block(*target)]),
            SwitchInt {
                discr: discriminant,
                targets,
            } => term::app(
                "TSwitchInt",
                vec![
                    self.operand(discriminant),
                    term::list(
                        targets
                            .iter()
                            .map(|(v, t)| term::pair(term::bits(v), basic_block(t)))
                            .collect(),
                    ),
                    basic_block(targets.otherwise()),
                ],
            ),
            UnwindResume => term::atom("TUnwindResume"),
            UnwindTerminate(r) => term::app("TUnwindTerminate", vec![terminate_reason(*r)]),
            Return => term::atom("TReturn"),
            Unreachable => term::atom("TUnreachable"),
            Drop {
                place,
                target,
                unwind,
                replace,
                drop,
            } => term::app(
                "TDrop",
                vec![
                    self.place(place),
                    basic_block(*target),
                    unwind_action(*unwind),
                    term::boolean(*replace),
                    term::option(drop.map(basic_block)),
                ],
            ),
            Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                fn_span,
            } => term::app(
                "TCall",
                vec![
                    self.operand(func),
                    term::list(args.iter().map(|a| self.operand(&a.node)).collect()),
                    self.place(destination),
                    term::option(target.map(basic_block)),
                    unwind_action(*unwind),
                    call_source_term(*call_source),
                    self.span(*fn_span),
                ],
            ),
            TailCall {
                func,
                args,
                fn_span,
            } => term::app(
                "TTailCall",
                vec![
                    self.operand(func),
                    term::list(args.iter().map(|a| self.operand(&a.node)).collect()),
                    self.span(*fn_span),
                ],
            ),
            Assert {
                cond,
                expected,
                msg: message,
                target,
                unwind,
            } => term::app(
                "TAssert",
                vec![
                    self.operand(cond),
                    term::boolean(*expected),
                    self.assert_kind(message),
                    basic_block(*target),
                    unwind_action(*unwind),
                ],
            ),
            Yield {
                value,
                resume,
                resume_arg,
                drop,
            } => term::app(
                "TYield",
                vec![
                    self.operand(value),
                    basic_block(*resume),
                    self.place(resume_arg),
                    term::option(drop.map(basic_block)),
                ],
            ),
            CoroutineDrop => term::atom("TCoroutineDrop"),
            FalseEdge {
                real_target,
                imaginary_target,
            } => term::app(
                "TFalseEdge",
                vec![basic_block(*real_target), basic_block(*imaginary_target)],
            ),
            FalseUnwind {
                real_target,
                unwind,
            } => term::app(
                "TFalseUnwind",
                vec![basic_block(*real_target), unwind_action(*unwind)],
            ),
            InlineAsm {
                asm_macro,
                template,
                operands,
                options,
                line_spans: _,
                targets,
                unwind,
            } => term::app(
                "TInlineAsm",
                vec![
                    term::atom(match asm_macro {
                        mir::InlineAsmMacro::Asm => "AmAsm",
                        mir::InlineAsmMacro::NakedAsm => "AmNakedAsm",
                    }),
                    term::list(
                        template
                            .iter()
                            .map(|p| term::string(&format!("{p:?}")))
                            .collect(),
                    ),
                    term::list(operands.iter().map(|o| self.asm_operand(o)).collect()),
                    term::list(vec![term::string(&format!("{options:?}"))]),
                    term::list(targets.iter().map(|t| basic_block(*t)).collect()),
                    unwind_action(*unwind),
                ],
            ),
        }
    }

    fn asm_operand(&self, o: &mir::InlineAsmOperand<'tcx>) -> Term {
        use mir::InlineAsmOperand::*;
        match o {
            In { reg, value } => term::app(
                "AoIn",
                vec![term::string(&format!("{reg:?}")), self.operand(value)],
            ),
            Out { reg, late, place } => term::app(
                "AoOut",
                vec![
                    term::string(&format!("{reg:?}")),
                    term::boolean(*late),
                    term::option(place.as_ref().map(|p| self.place(p))),
                ],
            ),
            InOut {
                reg,
                late,
                in_value,
                out_place,
            } => term::app(
                "AoInOut",
                vec![
                    term::string(&format!("{reg:?}")),
                    term::boolean(*late),
                    self.operand(in_value),
                    term::option(out_place.as_ref().map(|p| self.place(p))),
                ],
            ),
            Const { value } => term::app("AoConst", vec![self.const_operand(value)]),
            SymFn { value } => term::app("AoSymFn", vec![self.const_operand(value)]),
            SymStatic { def_id } => term::app("AoSymStatic", vec![self.path(*def_id)]),
            Label { target_index } => term::app("AoLabel", vec![term::nat(*target_index as u64)]),
        }
    }

    fn assert_kind(&self, k: &mir::AssertKind<mir::Operand<'tcx>>) -> Term {
        use mir::AssertKind::*;
        match k {
            BoundsCheck { len, index } => term::app(
                "AsBoundsCheck",
                vec![self.operand(len), self.operand(index)],
            ),
            Overflow(op, l, r) => term::app(
                "AsOverflow",
                vec![binary_op(*op), self.operand(l), self.operand(r)],
            ),
            OverflowNeg(o) => term::app("AsOverflowNeg", vec![self.operand(o)]),
            DivisionByZero(o) => term::app("AsDivisionByZero", vec![self.operand(o)]),
            RemainderByZero(o) => term::app("AsRemainderByZero", vec![self.operand(o)]),
            ResumedAfterReturn(c) => term::app(
                "AsResumedAfterReturn",
                vec![term::string(&format!("{c:?}"))],
            ),
            ResumedAfterPanic(c) => {
                term::app("AsResumedAfterPanic", vec![term::string(&format!("{c:?}"))])
            }
            ResumedAfterDrop(c) => {
                term::app("AsResumedAfterDrop", vec![term::string(&format!("{c:?}"))])
            }
            MisalignedPointerDereference { required, found } => term::app(
                "AsMisalignedPointerDereference",
                vec![self.operand(required), self.operand(found)],
            ),
            NullPointerDereference => term::atom("AsNullPointerDereference"),
            InvalidEnumConstruction(o) => {
                term::app("AsInvalidEnumConstruction", vec![self.operand(o)])
            }
        }
    }
}

fn debug_names(body: &mir::Body<'_>) -> BTreeMap<mir::Local, String> {
    let mut out = BTreeMap::new();
    for info in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(p) = info.value {
            if p.projection.is_empty() {
                out.entry(p.local).or_insert_with(|| info.name.to_string());
            }
        }
    }
    out
}

fn basic_block(b: mir::BasicBlock) -> Term {
    term::nat(b.as_u32() as u64)
}

fn const_value(v: mir::ConstValue) -> Term {
    match v {
        mir::ConstValue::Scalar(s) => term::app("CvScalar", vec![scalar(s)]),
        mir::ConstValue::ZeroSized => term::atom("CvZeroSized"),
        mir::ConstValue::Slice { alloc_id, meta } => term::app(
            "CvSlice",
            vec![
                term::string(&format!("{alloc_id:?}")),
                term::int(meta as i128),
            ],
        ),
        mir::ConstValue::Indirect { alloc_id, offset } => term::app(
            "CvIndirect",
            vec![
                term::string(&format!("{alloc_id:?}")),
                term::int(offset.bytes() as i128),
            ],
        ),
    }
}

fn scalar(s: mir::interpret::Scalar) -> Term {
    match s {
        mir::interpret::Scalar::Int(i) => term::app(
            "ScInt",
            vec![term::int(i.to_int(i.size())), term::nat(i.size().bytes())],
        ),
        mir::interpret::Scalar::Ptr(p, size) => {
            let (provenance, offset) = p.into_raw_parts();
            term::app(
                "ScPtr",
                vec![
                    term::string(&format!("{provenance:?}")),
                    term::int(offset.bytes() as i128),
                    term::nat(u64::from(size)),
                ],
            )
        }
    }
}

fn borrow_kind(borrow: mir::BorrowKind) -> Term {
    match borrow {
        mir::BorrowKind::Shared => term::atom("BkShared"),
        mir::BorrowKind::Fake(k) => term::app(
            "BkFake",
            vec![term::atom(match k {
                mir::FakeBorrowKind::Shallow => "FbShallow",
                mir::FakeBorrowKind::Deep => "FbDeep",
            })],
        ),
        mir::BorrowKind::Mut { kind } => term::app(
            "BkMut",
            vec![term::atom(match kind {
                mir::MutBorrowKind::Default => "MbDefault",
                mir::MutBorrowKind::TwoPhaseBorrow => "MbTwoPhase",
                mir::MutBorrowKind::ClosureCapture => "MbClosureCapture",
            })],
        ),
    }
}

fn raw_ptr_kind(k: mir::RawPtrKind) -> Term {
    term::atom(match k {
        mir::RawPtrKind::Mut => "RpMut",
        mir::RawPtrKind::Const => "RpConst",
        mir::RawPtrKind::FakeForPtrMetadata => "RpFakeForPtrMetadata",
    })
}

fn cast_kind(k: mir::CastKind) -> Term {
    use mir::CastKind::*;
    match k {
        PointerExposeProvenance => term::atom("CkPointerExposeProvenance"),
        PointerWithExposedProvenance => term::atom("CkPointerWithExposedProvenance"),
        PointerCoercion(coercion, source) => term::app(
            "CkPointerCoercion",
            vec![pointer_coercion(coercion), coercion_source(source)],
        ),
        IntToInt => term::atom("CkIntToInt"),
        FloatToInt => term::atom("CkFloatToInt"),
        FloatToFloat => term::atom("CkFloatToFloat"),
        IntToFloat => term::atom("CkIntToFloat"),
        PtrToPtr => term::atom("CkPtrToPtr"),
        FnPtrToPtr => term::atom("CkFnPtrToPtr"),
        Transmute => term::atom("CkTransmute"),
        Subtype => term::atom("CkSubtype"),
    }
}

fn pointer_coercion(coercion: ty::adjustment::PointerCoercion) -> Term {
    use ty::adjustment::PointerCoercion::*;
    match coercion {
        ReifyFnPointer(s) => term::app("PcReifyFnPointer", vec![types::safety(s)]),
        UnsafeFnPointer => term::atom("PcUnsafeFnPointer"),
        ClosureFnPointer(s) => term::app("PcClosureFnPointer", vec![types::safety(s)]),
        MutToConstPointer => term::atom("PcMutToConstPointer"),
        ArrayToPointer => term::atom("PcArrayToPointer"),
        Unsize => term::atom("PcUnsize"),
    }
}

fn coercion_source(s: mir::CoercionSource) -> Term {
    term::atom(match s {
        mir::CoercionSource::AsCast => "CoAsCast",
        mir::CoercionSource::Implicit => "CoImplicit",
    })
}

fn binary_op(op: mir::BinOp) -> Term {
    use mir::BinOp::*;
    term::atom(match op {
        Add => "BAdd",
        AddUnchecked => "BAddUnchecked",
        AddWithOverflow => "BAddWithOverflow",
        Sub => "BSub",
        SubUnchecked => "BSubUnchecked",
        SubWithOverflow => "BSubWithOverflow",
        Mul => "BMul",
        MulUnchecked => "BMulUnchecked",
        MulWithOverflow => "BMulWithOverflow",
        Div => "BDiv",
        Rem => "BRem",
        BitXor => "BBitXor",
        BitAnd => "BBitAnd",
        BitOr => "BBitOr",
        Shl => "BShl",
        ShlUnchecked => "BShlUnchecked",
        Shr => "BShr",
        ShrUnchecked => "BShrUnchecked",
        Eq => "BEq",
        Lt => "BLt",
        Le => "BLe",
        Ne => "BNe",
        Ge => "BGe",
        Gt => "BGt",
        Cmp => "BCmp",
        Offset => "BOffset",
    })
}

fn unary_op(op: mir::UnOp) -> Term {
    term::atom(match op {
        mir::UnOp::Not => "UNot",
        mir::UnOp::Neg => "UNeg",
        mir::UnOp::PtrMetadata => "UPtrMetadata",
    })
}

fn fake_read_cause(c: &mir::FakeReadCause) -> Term {
    use mir::FakeReadCause::*;
    match c {
        ForMatchGuard => term::atom("FrMatchGuard"),
        ForMatchedPlace(d) => term::app(
            "FrMatchedPlace",
            vec![term::option(d.map(|d| term::string(&format!("{d:?}"))))],
        ),
        ForGuardBinding => term::atom("FrGuardBinding"),
        ForLet(d) => term::app(
            "FrLet",
            vec![term::option(d.map(|d| term::string(&format!("{d:?}"))))],
        ),
        ForIndex => term::atom("FrIndex"),
    }
}

fn variance(v: ty::Variance) -> Term {
    term::atom(match v {
        ty::Variance::Covariant => "VCovariant",
        ty::Variance::Invariant => "VInvariant",
        ty::Variance::Contravariant => "VContravariant",
        ty::Variance::Bivariant => "VBivariant",
    })
}

fn terminate_reason(r: mir::UnwindTerminateReason) -> Term {
    term::atom(match r {
        mir::UnwindTerminateReason::Abi => "UtAbi",
        mir::UnwindTerminateReason::InCleanup => "UtInCleanup",
    })
}

fn unwind_action(u: mir::UnwindAction) -> Term {
    match u {
        mir::UnwindAction::Continue => term::atom("UaContinue"),
        mir::UnwindAction::Unreachable => term::atom("UaUnreachable"),
        mir::UnwindAction::Terminate(r) => term::app("UaTerminate", vec![terminate_reason(r)]),
        mir::UnwindAction::Cleanup(b) => term::app("UaCleanup", vec![basic_block(b)]),
    }
}

fn call_source_term(s: mir::CallSource) -> Term {
    term::atom(match s {
        mir::CallSource::OverloadedOperator => "SrcOverloadedOperator",
        mir::CallSource::MatchCmp => "SrcMatchCmp",
        mir::CallSource::Misc => "SrcMisc",
        mir::CallSource::Use => "SrcUse",
        mir::CallSource::Normal => "SrcNormal",
    })
}

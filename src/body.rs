use std::collections::BTreeMap;

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty;

use crate::rocq::{self, Term};
use crate::ty::{mutability, Cx};

impl<'tcx> Cx<'tcx> {
    pub fn body(
        &self,
        def_id: DefId,
        name: &str,
        body: &mir::Body<'tcx>,
        facts: Term,
    ) -> Term {
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
                rocq::note(label, rocq::app(
                    "LocalDecl",
                    vec![
                        self.ty(decl.ty),
                        mutability(decl.mutability),
                        rocq::option(names.get(&local).map(|n| rocq::string(n.clone()))),
                        self.span(decl.source_info.span),
                    ],
                ))
            })
            .collect();

        let blocks: Vec<Term> = body
            .basic_blocks
            .iter_enumerated()
            .map(|(bb, data)| {
                let label = if data.is_cleanup {
                    format!("bb{} (cleanup)", bb.as_u32())
                } else {
                    format!("bb{}", bb.as_u32())
                };
                rocq::note(label, rocq::app(
                    "BasicBlock",
                    vec![
                        rocq::nat(bb.as_u32() as u64),
                        rocq::list(data.statements.iter().map(|s| self.statement(s)).collect()),
                        match &data.terminator {
                            Some(t) => self.terminator(t),
                            None => rocq::app(
                                "Term",
                                vec![rocq::atom("NoSpan"), rocq::atom("TUnreachable")],
                            ),
                        },
                        rocq::boolean(data.is_cleanup),
                    ],
                ))
            })
            .collect();

        rocq::app(
            "Body",
            vec![
                rocq::note("name", rocq::string(name)),
                rocq::note("file", rocq::string(self.file())),
                rocq::note("span", self.span(body.span)),
                rocq::note("generics", self.generics(def_id)),
                rocq::note("bounds", self.bounds(def_id)),
                rocq::note("args", rocq::nat(body.arg_count as u64)),
                rocq::note("locals", rocq::list(locals)),
                rocq::note("blocks", rocq::list(blocks)),
                rocq::note(
                    "regions",
                    rocq::list(self.take_regions().into_iter().map(rocq::nat).collect()),
                ),
                rocq::note("polonius", facts),
            ],
        )
    }

    pub fn generics(&self, def_id: DefId) -> Term {
        let generics = self.tcx.generics_of(def_id);
        rocq::list(
            generics
                .own_params
                .iter()
                .map(|p| {
                    let idx = rocq::nat(p.index as u64);
                    let nm = rocq::string(p.name.to_string());
                    match p.kind {
                        ty::GenericParamDefKind::Lifetime => {
                            rocq::app("GpLifetime", vec![idx, nm])
                        }
                        ty::GenericParamDefKind::Type { .. } => rocq::app("GpTy", vec![idx, nm]),
                        ty::GenericParamDefKind::Const { .. } => rocq::app(
                            "GpConst",
                            vec![idx, nm, self.ty(self.tcx.type_of(p.def_id).skip_binder())],
                        ),
                    }
                })
                .collect(),
        )
    }

    pub fn bounds(&self, def_id: DefId) -> Term {
        rocq::list(
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
            ty::ClauseKind::Trait(t) => rocq::app(
                "BdTrait",
                vec![self.path(t.def_id()), self.generic_args(t.trait_ref.args)],
            ),
            ty::ClauseKind::Projection(p) => rocq::app(
                "BdProjection",
                vec![
                    self.path(p.projection_term.def_id()),
                    self.generic_args(p.projection_term.args),
                    match p.term.kind() {
                        ty::TermKind::Ty(t) => self.ty(t),
                        ty::TermKind::Const(c) => {
                            rocq::app("TError", vec![rocq::string(self.tconst(c).render())])
                        }
                    },
                ],
            ),
            ty::ClauseKind::RegionOutlives(o) => {
                rocq::app("BdOutlives", vec![self.region(o.0), self.region(o.1)])
            }
            ty::ClauseKind::TypeOutlives(o) => {
                rocq::app("BdTyOutlives", vec![self.ty(o.0), self.region(o.1)])
            }
            ty::ClauseKind::ConstArgHasType(c, t) => {
                rocq::app("BdConstArgHasType", vec![self.tconst(c), self.ty(t)])
            }
            ty::ClauseKind::WellFormed(term) => match term.kind() {
                ty::TermKind::Ty(t) => rocq::app("BdWellFormedTy", vec![self.ty(t)]),
                ty::TermKind::Const(c) => {
                    rocq::app("BdWellFormedConst", vec![self.tconst(c)])
                }
            },
            ty::ClauseKind::ConstEvaluatable(c) => {
                rocq::app("BdConstEvaluatable", vec![self.tconst(c)])
            }
            ty::ClauseKind::HostEffect(h) => rocq::app(
                "BdHostEffect",
                vec![
                    self.path(h.trait_ref.def_id),
                    self.generic_args(h.trait_ref.args),
                    rocq::string(format!("{:?}", h.constness)),
                ],
            ),
            ty::ClauseKind::UnstableFeature(sym) => {
                rocq::app("BdUnstableFeature", vec![rocq::string(sym.to_string())])
            }
        }
    }

    fn place(&self, p: &mir::Place<'tcx>) -> Term {
        rocq::app(
            "Place",
            vec![
                rocq::nat(p.local.as_u32() as u64),
                rocq::list(p.projection.iter().map(|e| self.proj_elem(e)).collect()),
            ],
        )
    }

    fn proj_elem(&self, e: mir::PlaceElem<'tcx>) -> Term {
        use mir::ProjectionElem::*;
        match e {
            Deref => rocq::atom("PDeref"),
            Field(idx, t) => {
                rocq::app("PField", vec![rocq::nat(idx.as_u32() as u64), self.ty(t)])
            }
            Index(l) => rocq::app("PIndex", vec![rocq::nat(l.as_u32() as u64)]),
            ConstantIndex { offset, min_length, from_end } => rocq::app(
                "PConstantIndex",
                vec![rocq::nat(offset), rocq::nat(min_length), rocq::boolean(from_end)],
            ),
            Subslice { from, to, from_end } => rocq::app(
                "PSubslice",
                vec![rocq::nat(from), rocq::nat(to), rocq::boolean(from_end)],
            ),
            Downcast(nm, v) => rocq::app(
                "PDowncast",
                vec![
                    rocq::option(nm.map(|s| rocq::string(s.to_string()))),
                    rocq::nat(v.as_u32() as u64),
                ],
            ),
            OpaqueCast(t) => rocq::app("POpaqueCast", vec![self.ty(t)]),
            UnwrapUnsafeBinder(t) => rocq::app("PUnwrapUnsafeBinder", vec![self.ty(t)]),
        }
    }

    fn operand(&self, o: &mir::Operand<'tcx>) -> Term {
        match o {
            mir::Operand::Copy(p) => rocq::app("OCopy", vec![self.place(p)]),
            mir::Operand::Move(p) => rocq::app("OMove", vec![self.place(p)]),
            mir::Operand::Constant(c) => rocq::app("OConst", vec![self.const_op(c)]),
            mir::Operand::RuntimeChecks(c) => rocq::app(
                "ORuntimeCheck",
                vec![rocq::atom(match c {
                    mir::RuntimeChecks::UbChecks => "RcUbChecks",
                    mir::RuntimeChecks::ContractChecks => "RcContractChecks",
                    mir::RuntimeChecks::OverflowChecks => "RcOverflowChecks",
                })],
            ),
        }
    }

    fn const_op(&self, c: &mir::ConstOperand<'tcx>) -> Term {
        rocq::app(
            "ConstOp",
            vec![self.span(c.span), self.constant(c.const_)],
        )
    }

    fn constant(&self, c: mir::Const<'tcx>) -> Term {
        match c {
            mir::Const::Ty(t, k) => rocq::app("KTy", vec![self.ty(t), self.tconst(k)]),
            mir::Const::Unevaluated(u, t) => rocq::app(
                "KUnevaluated",
                vec![
                    self.path(u.def),
                    self.generic_args(u.args),
                    rocq::option(u.promoted.map(|p| rocq::nat(p.as_u32() as u64))),
                    self.ty(t),
                ],
            ),
            mir::Const::Val(v, t) => rocq::app("KVal", vec![const_value(v), self.ty(t)]),
        }
    }

    fn rvalue(&self, r: &mir::Rvalue<'tcx>) -> Term {
        use mir::Rvalue::*;
        match r {
            Use(o, retag) => rocq::app(
                "RUse",
                vec![
                    self.operand(o),
                    rocq::atom(match retag {
                        mir::WithRetag::Yes => "RetagYes",
                        mir::WithRetag::No => "RetagNo",
                    }),
                ],
            ),
            Repeat(o, n) => rocq::app("RRepeat", vec![self.operand(o), self.tconst(*n)]),
            Ref(r, bk, p) => rocq::app(
                "RRef",
                vec![self.region(*r), borrow_kind(*bk), self.place(p)],
            ),
            ThreadLocalRef(def_id) => rocq::app("RThreadLocalRef", vec![self.path(*def_id)]),
            RawPtr(k, p) => rocq::app("RRawPtr", vec![raw_ptr_kind(*k), self.place(p)]),
            Cast(k, o, t) => {
                rocq::app("RCast", vec![cast_kind(*k), self.operand(o), self.ty(*t)])
            }
            BinaryOp(op, args) => rocq::app(
                "RBinaryOp",
                vec![bin_op(*op), self.operand(&args.0), self.operand(&args.1)],
            ),
            UnaryOp(op, o) => rocq::app("RUnaryOp", vec![un_op(*op), self.operand(o)]),
            Discriminant(p) => rocq::app("RDiscriminant", vec![self.place(p)]),
            Aggregate(k, fields) => rocq::app(
                "RAggregate",
                vec![
                    self.aggregate_kind(k),
                    rocq::list(fields.iter().map(|o| self.operand(o)).collect()),
                ],
            ),
            CopyForDeref(p) => rocq::app("RCopyForDeref", vec![self.place(p)]),
            WrapUnsafeBinder(o, t) => {
                rocq::app("RWrapUnsafeBinder", vec![self.operand(o), self.ty(*t)])
            }
            Reborrow(t, m, p) => rocq::app(
                "RReborrow",
                vec![self.ty(*t), mutability(*m), self.place(p)],
            ),
        }
    }

    fn aggregate_kind(&self, k: &mir::AggregateKind<'tcx>) -> Term {
        use mir::AggregateKind::*;
        match k {
            Array(t) => rocq::app("AgArray", vec![self.ty(*t)]),
            Tuple => rocq::atom("AgTuple"),
            Adt(def_id, v, args, _user_ty, active) => rocq::app(
                "AgAdt",
                vec![
                    self.path(*def_id),
                    rocq::nat(v.as_u32() as u64),
                    self.generic_args(args),
                    rocq::option(active.map(|f| rocq::nat(f.as_u32() as u64))),
                ],
            ),
            Closure(def_id, args) => {
                rocq::app("AgClosure", vec![self.path(*def_id), self.generic_args(args)])
            }
            Coroutine(def_id, args) => rocq::app(
                "AgCoroutine",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            CoroutineClosure(def_id, args) => rocq::app(
                "AgCoroutineClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            RawPtr(t, m) => rocq::app("AgRawPtr", vec![self.ty(*t), mutability(*m)]),
        }
    }

    fn statement(&self, s: &mir::Statement<'tcx>) -> Term {
        rocq::app(
            "Stmt",
            vec![self.span(s.source_info.span), self.statement_kind(&s.kind)],
        )
    }

    fn statement_kind(&self, k: &mir::StatementKind<'tcx>) -> Term {
        use mir::StatementKind::*;
        match k {
            Assign(b) => rocq::app("SAssign", vec![self.place(&b.0), self.rvalue(&b.1)]),
            FakeRead(b) => rocq::app(
                "SFakeRead",
                vec![fake_read_cause(&b.0), self.place(&b.1)],
            ),
            SetDiscriminant { place, variant_index } => rocq::app(
                "SSetDiscriminant",
                vec![self.place(place), rocq::nat(variant_index.as_u32() as u64)],
            ),
            StorageLive(l) => rocq::app("SStorageLive", vec![rocq::nat(l.as_u32() as u64)]),
            StorageDead(l) => rocq::app("SStorageDead", vec![rocq::nat(l.as_u32() as u64)]),
            PlaceMention(p) => rocq::app("SPlaceMention", vec![self.place(p)]),
            AscribeUserType(b, var) => rocq::app(
                "SAscribeUserType",
                vec![
                    self.place(&b.0),
                    rocq::string(format!("{:?}", b.1)),
                    variance(*var),
                ],
            ),
            Coverage(kind) => {
                rocq::app("SCoverage", vec![rocq::string(format!("{kind:?}"))])
            }
            Intrinsic(i) => rocq::app("SIntrinsic", vec![self.nd_intrinsic(i)]),
            ConstEvalCounter => rocq::atom("SConstEvalCounter"),
            Nop => rocq::atom("SNop"),
            BackwardIncompatibleDropHint { place, reason } => rocq::app(
                "SBackwardIncompatibleDropHint",
                vec![self.place(place), rocq::string(format!("{reason:?}"))],
            ),
        }
    }

    fn nd_intrinsic(&self, i: &mir::NonDivergingIntrinsic<'tcx>) -> Term {
        match i {
            mir::NonDivergingIntrinsic::Assume(o) => {
                rocq::app("NiAssume", vec![self.operand(o)])
            }
            mir::NonDivergingIntrinsic::CopyNonOverlapping(c) => rocq::app(
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
        rocq::app(
            "Term",
            vec![self.span(t.source_info.span), self.terminator_kind(&t.kind)],
        )
    }

    fn terminator_kind(&self, k: &mir::TerminatorKind<'tcx>) -> Term {
        use mir::TerminatorKind::*;
        match k {
            Goto { target } => rocq::app("TGoto", vec![bb(*target)]),
            SwitchInt { discr, targets } => rocq::app(
                "TSwitchInt",
                vec![
                    self.operand(discr),
                    rocq::list(
                        targets
                            .iter()
                            .map(|(v, t)| rocq::pair(rocq::int(v as i128), bb(t)))
                            .collect(),
                    ),
                    bb(targets.otherwise()),
                ],
            ),
            UnwindResume => rocq::atom("TUnwindResume"),
            UnwindTerminate(r) => rocq::app("TUnwindTerminate", vec![terminate_reason(*r)]),
            Return => rocq::atom("TReturn"),
            Unreachable => rocq::atom("TUnreachable"),
            Drop { place, target, unwind, replace, drop } => rocq::app(
                "TDrop",
                vec![
                    self.place(place),
                    bb(*target),
                    unwind_action(*unwind),
                    rocq::boolean(*replace),
                    rocq::option(drop.map(bb)),
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
            } => rocq::app(
                "TCall",
                vec![
                    self.operand(func),
                    rocq::list(args.iter().map(|a| self.operand(&a.node)).collect()),
                    self.place(destination),
                    rocq::option(target.map(bb)),
                    unwind_action(*unwind),
                    call_source_term(*call_source),
                    self.span(*fn_span),
                ],
            ),
            TailCall { func, args, fn_span } => rocq::app(
                "TTailCall",
                vec![
                    self.operand(func),
                    rocq::list(args.iter().map(|a| self.operand(&a.node)).collect()),
                    self.span(*fn_span),
                ],
            ),
            Assert { cond, expected, msg, target, unwind } => rocq::app(
                "TAssert",
                vec![
                    self.operand(cond),
                    rocq::boolean(*expected),
                    self.assert_kind(msg),
                    bb(*target),
                    unwind_action(*unwind),
                ],
            ),
            Yield { value, resume, resume_arg, drop } => rocq::app(
                "TYield",
                vec![
                    self.operand(value),
                    bb(*resume),
                    self.place(resume_arg),
                    rocq::option(drop.map(bb)),
                ],
            ),
            CoroutineDrop => rocq::atom("TCoroutineDrop"),
            FalseEdge { real_target, imaginary_target } => rocq::app(
                "TFalseEdge",
                vec![bb(*real_target), bb(*imaginary_target)],
            ),
            FalseUnwind { real_target, unwind } => rocq::app(
                "TFalseUnwind",
                vec![bb(*real_target), unwind_action(*unwind)],
            ),
            InlineAsm {
                asm_macro,
                template,
                operands,
                options,
                line_spans: _,
                targets,
                unwind,
            } => rocq::app(
                "TInlineAsm",
                vec![
                    rocq::atom(match asm_macro {
                        mir::InlineAsmMacro::Asm => "AmAsm",
                        mir::InlineAsmMacro::NakedAsm => "AmNakedAsm",
                    }),
                    rocq::list(
                        template
                            .iter()
                            .map(|p| rocq::string(format!("{p:?}")))
                            .collect(),
                    ),
                    rocq::list(operands.iter().map(|o| self.asm_operand(o)).collect()),
                    rocq::list(vec![rocq::string(format!("{options:?}"))]),
                    rocq::list(targets.iter().map(|t| bb(*t)).collect()),
                    unwind_action(*unwind),
                ],
            ),
        }
    }

    fn asm_operand(&self, o: &mir::InlineAsmOperand<'tcx>) -> Term {
        use mir::InlineAsmOperand::*;
        match o {
            In { reg, value } => {
                rocq::app("AoIn", vec![rocq::string(format!("{reg:?}")), self.operand(value)])
            }
            Out { reg, late, place } => rocq::app(
                "AoOut",
                vec![
                    rocq::string(format!("{reg:?}")),
                    rocq::boolean(*late),
                    rocq::option(place.as_ref().map(|p| self.place(p))),
                ],
            ),
            InOut { reg, late, in_value, out_place } => rocq::app(
                "AoInOut",
                vec![
                    rocq::string(format!("{reg:?}")),
                    rocq::boolean(*late),
                    self.operand(in_value),
                    rocq::option(out_place.as_ref().map(|p| self.place(p))),
                ],
            ),
            Const { value } => rocq::app("AoConst", vec![self.const_op(value)]),
            SymFn { value } => rocq::app("AoSymFn", vec![self.const_op(value)]),
            SymStatic { def_id } => rocq::app("AoSymStatic", vec![self.path(*def_id)]),
            Label { target_index } => {
                rocq::app("AoLabel", vec![rocq::nat(*target_index as u64)])
            }
        }
    }

    fn assert_kind(&self, k: &mir::AssertKind<mir::Operand<'tcx>>) -> Term {
        use mir::AssertKind::*;
        match k {
            BoundsCheck { len, index } => {
                rocq::app("AsBoundsCheck", vec![self.operand(len), self.operand(index)])
            }
            Overflow(op, l, r) => rocq::app(
                "AsOverflow",
                vec![bin_op(*op), self.operand(l), self.operand(r)],
            ),
            OverflowNeg(o) => rocq::app("AsOverflowNeg", vec![self.operand(o)]),
            DivisionByZero(o) => rocq::app("AsDivisionByZero", vec![self.operand(o)]),
            RemainderByZero(o) => rocq::app("AsRemainderByZero", vec![self.operand(o)]),
            ResumedAfterReturn(c) => {
                rocq::app("AsResumedAfterReturn", vec![rocq::string(format!("{c:?}"))])
            }
            ResumedAfterPanic(c) => {
                rocq::app("AsResumedAfterPanic", vec![rocq::string(format!("{c:?}"))])
            }
            ResumedAfterDrop(c) => {
                rocq::app("AsResumedAfterDrop", vec![rocq::string(format!("{c:?}"))])
            }
            MisalignedPointerDereference { required, found } => rocq::app(
                "AsMisalignedPointerDereference",
                vec![self.operand(required), self.operand(found)],
            ),
            NullPointerDereference => rocq::atom("AsNullPointerDereference"),
            InvalidEnumConstruction(o) => {
                rocq::app("AsInvalidEnumConstruction", vec![self.operand(o)])
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

fn bb(b: mir::BasicBlock) -> Term {
    rocq::nat(b.as_u32() as u64)
}

fn const_value(v: mir::ConstValue) -> Term {
    match v {
        mir::ConstValue::Scalar(s) => rocq::app("CvScalar", vec![scalar(s)]),
        mir::ConstValue::ZeroSized => rocq::atom("CvZeroSized"),
        mir::ConstValue::Slice { alloc_id, meta } => rocq::app(
            "CvSlice",
            vec![rocq::string(format!("{alloc_id:?}")), rocq::int(meta as i128)],
        ),
        mir::ConstValue::Indirect { alloc_id, offset } => rocq::app(
            "CvIndirect",
            vec![
                rocq::string(format!("{alloc_id:?}")),
                rocq::int(offset.bytes() as i128),
            ],
        ),
    }
}

fn scalar(s: mir::interpret::Scalar) -> Term {
    match s {
        mir::interpret::Scalar::Int(i) => rocq::app(
            "ScInt",
            vec![
                rocq::int(i.to_int(i.size())),
                rocq::nat(i.size().bytes()),
            ],
        ),
        mir::interpret::Scalar::Ptr(p, size) => {
            let (prov, offset) = p.into_raw_parts();
            rocq::app(
                "ScPtr",
                vec![
                    rocq::string(format!("{prov:?}")),
                    rocq::int(offset.bytes() as i128),
                    rocq::nat(size),
                ],
            )
        }
    }
}

fn borrow_kind(bk: mir::BorrowKind) -> Term {
    match bk {
        mir::BorrowKind::Shared => rocq::atom("BkShared"),
        mir::BorrowKind::Fake(k) => rocq::app(
            "BkFake",
            vec![rocq::atom(match k {
                mir::FakeBorrowKind::Shallow => "FbShallow",
                mir::FakeBorrowKind::Deep => "FbDeep",
            })],
        ),
        mir::BorrowKind::Mut { kind } => rocq::app(
            "BkMut",
            vec![rocq::atom(match kind {
                mir::MutBorrowKind::Default => "MbDefault",
                mir::MutBorrowKind::TwoPhaseBorrow => "MbTwoPhase",
                mir::MutBorrowKind::ClosureCapture => "MbClosureCapture",
            })],
        ),
    }
}

fn raw_ptr_kind(k: mir::RawPtrKind) -> Term {
    rocq::atom(match k {
        mir::RawPtrKind::Mut => "RpMut",
        mir::RawPtrKind::Const => "RpConst",
        mir::RawPtrKind::FakeForPtrMetadata => "RpFakeForPtrMetadata",
    })
}

fn cast_kind(k: mir::CastKind) -> Term {
    use mir::CastKind::*;
    match k {
        PointerExposeProvenance => rocq::atom("CkPointerExposeProvenance"),
        PointerWithExposedProvenance => rocq::atom("CkPointerWithExposedProvenance"),
        PointerCoercion(pc, src) => rocq::app(
            "CkPointerCoercion",
            vec![pointer_coercion(pc), coercion_source(src)],
        ),
        IntToInt => rocq::atom("CkIntToInt"),
        FloatToInt => rocq::atom("CkFloatToInt"),
        FloatToFloat => rocq::atom("CkFloatToFloat"),
        IntToFloat => rocq::atom("CkIntToFloat"),
        PtrToPtr => rocq::atom("CkPtrToPtr"),
        FnPtrToPtr => rocq::atom("CkFnPtrToPtr"),
        Transmute => rocq::atom("CkTransmute"),
        Subtype => rocq::atom("CkSubtype"),
    }
}

fn pointer_coercion(pc: ty::adjustment::PointerCoercion) -> Term {
    use ty::adjustment::PointerCoercion::*;
    match pc {
        ReifyFnPointer(s) => rocq::app("PcReifyFnPointer", vec![safety(s)]),
        UnsafeFnPointer => rocq::atom("PcUnsafeFnPointer"),
        ClosureFnPointer(s) => rocq::app("PcClosureFnPointer", vec![safety(s)]),
        MutToConstPointer => rocq::atom("PcMutToConstPointer"),
        ArrayToPointer => rocq::atom("PcArrayToPointer"),
        Unsize => rocq::atom("PcUnsize"),
    }
}

fn safety(s: rustc_hir::Safety) -> Term {
    rocq::atom(match s {
        rustc_hir::Safety::Safe => "Safe",
        rustc_hir::Safety::Unsafe => "Unsafe",
    })
}

fn coercion_source(s: mir::CoercionSource) -> Term {
    rocq::atom(match s {
        mir::CoercionSource::AsCast => "CoAsCast",
        mir::CoercionSource::Implicit => "CoImplicit",
    })
}

fn bin_op(op: mir::BinOp) -> Term {
    use mir::BinOp::*;
    rocq::atom(match op {
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

fn un_op(op: mir::UnOp) -> Term {
    rocq::atom(match op {
        mir::UnOp::Not => "UNot",
        mir::UnOp::Neg => "UNeg",
        mir::UnOp::PtrMetadata => "UPtrMetadata",
    })
}

fn fake_read_cause(c: &mir::FakeReadCause) -> Term {
    use mir::FakeReadCause::*;
    match c {
        ForMatchGuard => rocq::atom("FrMatchGuard"),
        ForMatchedPlace(d) => rocq::app(
            "FrMatchedPlace",
            vec![rocq::option(d.map(|d| rocq::string(format!("{d:?}"))))],
        ),
        ForGuardBinding => rocq::atom("FrGuardBinding"),
        ForLet(d) => rocq::app(
            "FrLet",
            vec![rocq::option(d.map(|d| rocq::string(format!("{d:?}"))))],
        ),
        ForIndex => rocq::atom("FrIndex"),
    }
}

fn variance(v: ty::Variance) -> Term {
    rocq::atom(match v {
        ty::Variance::Covariant => "VCovariant",
        ty::Variance::Invariant => "VInvariant",
        ty::Variance::Contravariant => "VContravariant",
        ty::Variance::Bivariant => "VBivariant",
    })
}

fn terminate_reason(r: mir::UnwindTerminateReason) -> Term {
    rocq::atom(match r {
        mir::UnwindTerminateReason::Abi => "UtAbi",
        mir::UnwindTerminateReason::InCleanup => "UtInCleanup",
    })
}

fn unwind_action(u: mir::UnwindAction) -> Term {
    match u {
        mir::UnwindAction::Continue => rocq::atom("UaContinue"),
        mir::UnwindAction::Unreachable => rocq::atom("UaUnreachable"),
        mir::UnwindAction::Terminate(r) => {
            rocq::app("UaTerminate", vec![terminate_reason(r)])
        }
        mir::UnwindAction::Cleanup(b) => rocq::app("UaCleanup", vec![bb(b)]),
    }
}

fn call_source_term(s: mir::CallSource) -> Term {
    rocq::atom(match s {
        mir::CallSource::OverloadedOperator => "SrcOverloadedOperator",
        mir::CallSource::MatchCmp => "SrcMatchCmp",
        mir::CallSource::Misc => "SrcMisc",
        mir::CallSource::Use => "SrcUse",
        mir::CallSource::Normal => "SrcNormal",
    })
}

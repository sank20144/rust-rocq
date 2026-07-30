use rustc_middle::ty::{self, Ty, TyCtxt, ValTreeKindExt as _};
use rustc_type_ir::{ConstKind, RegionKind, TyKind, UnevaluatedConstKind};
use rustc_span::Span;

use crate::rocq::{self, Term};

pub struct Cx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> Cx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Cx { tcx }
    }

    pub fn path(&self, def_id: rustc_hir::def_id::DefId) -> Term {
        rocq::string(self.tcx.def_path_str(def_id))
    }

    pub fn span(&self, span: Span) -> Term {
        if span.is_dummy() {
            return rocq::atom("NoSpan");
        }
        let sm = self.tcx.sess.source_map();
        let Ok(lo) = sm.lookup_line(span.lo()) else {
            return rocq::atom("NoSpan");
        };
        let Ok(hi) = sm.lookup_line(span.hi()) else {
            return rocq::atom("NoSpan");
        };
        let file = sm.filename_for_diagnostics(&lo.sf.name).to_string();
        let lo_col = sm.lookup_char_pos(span.lo()).col_display;
        let hi_col = sm.lookup_char_pos(span.hi()).col_display;
        rocq::app(
            "Span",
            vec![
                rocq::string(file),
                rocq::nat(lo.line as u64 + 1),
                rocq::nat(lo_col as u64),
                rocq::nat(hi.line as u64 + 1),
                rocq::nat(hi_col as u64),
            ],
        )
    }

    pub fn ty(&self, t: Ty<'tcx>) -> Term {
        use TyKind::*;
        match t.kind() {
            Bool => rocq::atom("TBool"),
            Char => rocq::atom("TChar"),
            Int(i) => rocq::app("TInt", vec![int_width(*i)]),
            Uint(u) => rocq::app("TUint", vec![uint_width(*u)]),
            Float(f) => rocq::app("TFloat", vec![float_width(*f)]),
            Adt(def, args) => rocq::app(
                "TAdt",
                vec![self.path(def.did()), self.generic_args(args)],
            ),
            Foreign(def_id) => rocq::app("TForeign", vec![self.path(*def_id)]),
            Str => rocq::atom("TStr"),
            Array(elem, len) => rocq::app("TArray", vec![self.ty(*elem), self.tconst(*len)]),
            Pat(base, pat) => rocq::app("TPat", vec![self.ty(*base), self.ty_pat(*pat)]),
            Slice(elem) => rocq::app("TSlice", vec![self.ty(*elem)]),
            RawPtr(pointee, m) => {
                rocq::app("TRawPtr", vec![self.ty(*pointee), mutability(*m)])
            }
            Ref(r, pointee, m) => rocq::app(
                "TRef",
                vec![self.region(*r), self.ty(*pointee), mutability(*m)],
            ),
            FnDef(def_id, args) => {
                rocq::app("TFnDef", vec![self.path(*def_id), self.generic_args(args)])
            }
            FnPtr(sig_tys, hdr) => {
                rocq::app("TFnPtr", vec![self.fn_sig(*sig_tys, *hdr)])
            }
            UnsafeBinder(b) => rocq::app("TUnsafeBinder", vec![self.ty(b.skip_binder())]),
            Dynamic(preds, r) => rocq::app(
                "TDynamic",
                vec![self.dyn_preds(preds), self.region(*r)],
            ),
            Closure(def_id, args) => {
                rocq::app("TClosure", vec![self.path(*def_id), self.generic_args(args)])
            }
            CoroutineClosure(def_id, args) => rocq::app(
                "TCoroutineClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            Coroutine(def_id, args) => rocq::app(
                "TCoroutine",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            CoroutineWitness(def_id, args) => rocq::app(
                "TCoroutineWitness",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            Never => rocq::atom("TNever"),
            Tuple(elems) => rocq::app(
                "TTuple",
                vec![rocq::list(elems.iter().map(|t| self.ty(t)).collect())],
            ),
            Alias(alias) => rocq::app(
                "TAlias",
                vec![
                    alias_kind(alias.kind),
                    self.path(alias.kind.def_id()),
                    self.generic_args(alias.args),
                ],
            ),
            Param(p) => rocq::app(
                "TParam",
                vec![rocq::nat(p.index as u64), rocq::string(p.name.to_string())],
            ),
            Bound(depth, b) => rocq::app(
                "TBound",
                vec![bound_depth(*depth), rocq::nat(b.var.as_u32() as u64)],
            ),
            Placeholder(p) => rocq::app(
                "TPlaceholder",
                vec![
                    rocq::nat(p.universe.as_u32() as u64),
                    rocq::nat(p.bound.var.as_u32() as u64),
                ],
            ),
            Infer(_) => error("infer type after typeck"),
            Error(_) => error("type error"),
        }
    }

    fn ty_pat(&self, pat: ty::Pattern<'tcx>) -> Term {
        match &*pat {
            ty::PatternKind::Range { start, end } => {
                rocq::app("PatRange", vec![self.tconst(*start), self.tconst(*end)])
            }
            ty::PatternKind::Or(alts) => rocq::app(
                "PatOr",
                vec![rocq::list(alts.iter().map(|p| self.ty_pat(p)).collect())],
            ),
            ty::PatternKind::NotNull => rocq::app(
                "PatRange",
                vec![
                    rocq::app("CError", vec![rocq::string("not-null")]),
                    rocq::app("CError", vec![rocq::string("not-null")]),
                ],
            ),
        }
    }

    pub fn region(&self, r: ty::Region<'tcx>) -> Term {
        use RegionKind::*;
        match r.kind() {
            ReVar(vid) => rocq::app("RVar", vec![rocq::nat(vid.as_u32() as u64)]),
            ReEarlyParam(p) => rocq::app(
                "RParam",
                vec![rocq::nat(p.index as u64), rocq::string(p.name.to_string())],
            ),
            ReLateParam(p) => rocq::app(
                "RParam",
                vec![rocq::nat(0u32), rocq::string(format!("{:?}", p.kind))],
            ),
            ReBound(depth, br) => rocq::app(
                "RBound",
                vec![bound_depth(depth), rocq::nat(br.var.as_u32() as u64)],
            ),
            RePlaceholder(p) => rocq::app(
                "RPlaceholder",
                vec![
                    rocq::nat(p.universe.as_u32() as u64),
                    rocq::nat(p.bound.var.as_u32() as u64),
                ],
            ),
            ReStatic => rocq::atom("RStatic"),
            ReErased => rocq::atom("RErased"),
            ReError(_) => rocq::app("RError", vec![rocq::string("region error")]),
        }
    }

    pub fn tconst(&self, c: ty::Const<'tcx>) -> Term {
        match c.kind() {
            ConstKind::Param(p) => rocq::app(
                "CParam",
                vec![rocq::nat(p.index as u64), rocq::string(p.name.to_string())],
            ),
            ConstKind::Value(v) => {
                let t = self.ty(v.ty);
                match v.valtree.try_to_scalar().and_then(|s| s.try_to_scalar_int().ok()) {
                    Some(s) => rocq::app("CValue", vec![t, rocq::int(s.to_int(s.size()))]),
                    None => rocq::app("CError", vec![rocq::string("non-scalar valtree")]),
                }
            }
            ConstKind::Unevaluated(u) => {
                let def_id = match u.kind {
                    UnevaluatedConstKind::Projection { def_id }
                    | UnevaluatedConstKind::Inherent { def_id }
                    | UnevaluatedConstKind::Free { def_id }
                    | UnevaluatedConstKind::Anon { def_id } => def_id,
                };
                rocq::app("CUnevaluated", vec![self.path(def_id), self.generic_args(u.args)])
            }
            ConstKind::Bound(depth, var) => rocq::app(
                "CBound",
                vec![bound_depth(depth), rocq::nat(var.var.as_u32() as u64)],
            ),
            ConstKind::Infer(_) => {
                rocq::app("CError", vec![rocq::string("infer const after typeck")])
            }
            ConstKind::Placeholder(p) => rocq::app(
                "CError",
                vec![rocq::string(format!("placeholder const {:?}", p))],
            ),
            ConstKind::Expr(_) => {
                rocq::app("CError", vec![rocq::string("const expr")])
            }
            ConstKind::Error(_) => rocq::app("CError", vec![rocq::string("const error")]),
        }
    }

    pub fn generic_args(&self, args: ty::GenericArgsRef<'tcx>) -> Term {
        rocq::list(
            args.iter()
                .map(|a| match a.kind() {
                    ty::GenericArgKind::Type(t) => rocq::app("GTy", vec![self.ty(t)]),
                    ty::GenericArgKind::Lifetime(r) => {
                        rocq::app("GLifetime", vec![self.region(r)])
                    }
                    ty::GenericArgKind::Const(c) => rocq::app("GConst", vec![self.tconst(c)]),
                })
                .collect(),
        )
    }

    fn fn_sig(&self, sig_tys: ty::Binder<'tcx, ty::FnSigTys<TyCtxt<'tcx>>>, hdr: ty::FnHeader<TyCtxt<'tcx>>) -> Term {
        let tys = sig_tys.skip_binder();
        let inputs: Vec<Term> = tys.inputs().iter().map(|t| self.ty(*t)).collect();
        rocq::app(
            "FnSig",
            vec![
                rocq::list(inputs),
                self.ty(tys.output()),
                rocq::boolean(hdr.c_variadic()),
                safety(hdr.safety()),
                rocq::string(format!("{:?}", hdr.abi())),
            ],
        )
    }

    fn dyn_preds(&self, preds: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>) -> Term {
        rocq::list(
            preds
                .iter()
                .map(|p| match p.skip_binder() {
                    ty::ExistentialPredicate::Trait(t) => {
                        rocq::app("DTrait", vec![self.path(t.def_id), self.generic_args(t.args)])
                    }
                    ty::ExistentialPredicate::Projection(p) => rocq::app(
                        "DProjection",
                        vec![
                            self.path(p.def_id),
                            self.generic_args(p.args),
                            match p.term.kind() {
                                ty::TermKind::Ty(t) => self.ty(t),
                                ty::TermKind::Const(c) => {
                                    rocq::app("TError", vec![rocq::string(self.tconst(c).render())])
                                }
                            },
                        ],
                    ),
                    ty::ExistentialPredicate::AutoTrait(def_id) => {
                        rocq::app("DAutoTrait", vec![self.path(def_id)])
                    }
                })
                .collect(),
        )
    }
}

fn error(msg: &str) -> Term {
    rocq::app("TError", vec![rocq::string(msg)])
}

fn int_width(i: ty::IntTy) -> Term {
    rocq::atom(match i {
        ty::IntTy::Isize => "WSize",
        ty::IntTy::I8 => "W8",
        ty::IntTy::I16 => "W16",
        ty::IntTy::I32 => "W32",
        ty::IntTy::I64 => "W64",
        ty::IntTy::I128 => "W128",
    })
}

fn uint_width(u: ty::UintTy) -> Term {
    rocq::atom(match u {
        ty::UintTy::Usize => "WSize",
        ty::UintTy::U8 => "W8",
        ty::UintTy::U16 => "W16",
        ty::UintTy::U32 => "W32",
        ty::UintTy::U64 => "W64",
        ty::UintTy::U128 => "W128",
    })
}

fn float_width(f: ty::FloatTy) -> Term {
    rocq::atom(match f {
        ty::FloatTy::F16 => "FW16",
        ty::FloatTy::F32 => "FW32",
        ty::FloatTy::F64 => "FW64",
        ty::FloatTy::F128 => "FW128",
    })
}

pub fn mutability(m: rustc_middle::mir::Mutability) -> Term {
    rocq::atom(match m {
        rustc_middle::mir::Mutability::Mut => "Mut",
        rustc_middle::mir::Mutability::Not => "Imm",
    })
}

fn safety(s: rustc_hir::Safety) -> Term {
    rocq::atom(match s {
        rustc_hir::Safety::Safe => "Safe",
        rustc_hir::Safety::Unsafe => "Unsafe",
    })
}

fn alias_kind(k: ty::AliasTyKind) -> Term {
    rocq::atom(match k {
        ty::AliasTyKind::Projection { .. } => "AkProjection",
        ty::AliasTyKind::Inherent { .. } => "AkInherent",
        ty::AliasTyKind::Opaque { .. } => "AkOpaque",
        ty::AliasTyKind::Free { .. } => "AkFree",
    })
}

fn bound_depth(d: rustc_type_ir::BoundVarIndexKind) -> Term {
    match d {
        rustc_type_ir::BoundVarIndexKind::Bound(i) => {
            rocq::app("BdIndex", vec![rocq::nat(i.as_u32() as u64)])
        }
        rustc_type_ir::BoundVarIndexKind::Canonical => rocq::atom("BdCanonical"),
    }
}

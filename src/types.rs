use rustc_middle::ty::{self, Ty, TyCtxt, ValTreeKindExt as _};
use rustc_type_ir::{ConstKind, RegionKind, TyKind, UnevaluatedConstKind};

use crate::term::{self, Term};
use crate::translator::Translator;

impl<'tcx> Translator<'tcx> {
    pub fn ty(&self, t: Ty<'tcx>) -> Term {
        use TyKind::*;
        match t.kind() {
            Bool => term::atom("TBool"),
            Char => term::atom("TChar"),
            Int(i) => term::app("TInt", vec![int_width(*i)]),
            Uint(u) => term::app("TUint", vec![uint_width(*u)]),
            Float(f) => term::app("TFloat", vec![float_width(*f)]),
            Adt(def, args) => {
                let did = def.did();
                self.record_adt(did);
                term::app("TAdt", vec![self.path(did), self.generic_args(args)])
            }
            Foreign(def_id) => term::app("TForeign", vec![self.path(*def_id)]),
            Str => term::atom("TStr"),
            Array(elem, len) => term::app("TArray", vec![self.ty(*elem), self.tconst(*len)]),
            Pat(base, pat) => term::app("TPat", vec![self.ty(*base), self.ty_pat(*pat)]),
            Slice(elem) => term::app("TSlice", vec![self.ty(*elem)]),
            RawPtr(pointee, m) => term::app("TRawPtr", vec![self.ty(*pointee), mutability(*m)]),
            Ref(r, pointee, m) => term::app(
                "TRef",
                vec![self.region(*r), self.ty(*pointee), mutability(*m)],
            ),
            FnDef(def_id, args) => {
                term::app("TFnDef", vec![self.path(*def_id), self.generic_args(args)])
            }
            FnPtr(sig_tys, hdr) => term::app("TFnPtr", vec![self.fn_sig(*sig_tys, *hdr)]),
            UnsafeBinder(b) => term::app("TUnsafeBinder", vec![self.ty(b.skip_binder())]),
            Dynamic(preds, r) => {
                term::app("TDynamic", vec![self.dyn_preds(preds), self.region(*r)])
            }
            Closure(def_id, args) => term::app(
                "TClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            CoroutineClosure(def_id, args) => term::app(
                "TCoroutineClosure",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            Coroutine(def_id, args) => term::app(
                "TCoroutine",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            CoroutineWitness(def_id, args) => term::app(
                "TCoroutineWitness",
                vec![self.path(*def_id), self.generic_args(args)],
            ),
            Never => term::atom("TNever"),
            Tuple(elems) => term::app(
                "TTuple",
                vec![term::list(elems.iter().map(|t| self.ty(t)).collect())],
            ),
            Alias(alias) => term::app(
                "TAlias",
                vec![
                    alias_kind(alias.kind),
                    self.path(alias.kind.def_id()),
                    self.generic_args(alias.args),
                ],
            ),
            Param(p) => term::app(
                "TParam",
                vec![term::nat(p.index as u64), term::string(p.name.to_string())],
            ),
            Bound(depth, b) => term::app(
                "TBound",
                vec![bound_depth(*depth), term::nat(b.var.as_u32() as u64)],
            ),
            Placeholder(p) => term::app(
                "TPlaceholder",
                vec![
                    term::nat(p.universe.as_u32() as u64),
                    term::nat(p.bound.var.as_u32() as u64),
                ],
            ),
            Infer(_) => error("infer type after typeck"),
            Error(_) => error("type error"),
        }
    }

    fn ty_pat(&self, pat: ty::Pattern<'tcx>) -> Term {
        match &*pat {
            ty::PatternKind::Range { start, end } => {
                term::app("PatRange", vec![self.tconst(*start), self.tconst(*end)])
            }
            ty::PatternKind::Or(alts) => term::app(
                "PatOr",
                vec![term::list(alts.iter().map(|p| self.ty_pat(p)).collect())],
            ),
            ty::PatternKind::NotNull => term::atom("PatNotNull"),
        }
    }

    pub fn region(&self, r: ty::Region<'tcx>) -> Term {
        use RegionKind::*;
        match r.kind() {
            ReVar(vid) => {
                self.record_region(vid.as_u32());
                term::app("RVar", vec![term::nat(vid.as_u32() as u64)])
            }
            ReEarlyParam(p) => term::app(
                "RParam",
                vec![term::nat(p.index as u64), term::string(p.name.to_string())],
            ),
            ReLateParam(p) => term::app(
                "RParam",
                vec![term::nat(0u32), term::string(format!("{:?}", p.kind))],
            ),
            ReBound(depth, br) => term::app(
                "RBound",
                vec![bound_depth(depth), term::nat(br.var.as_u32() as u64)],
            ),
            RePlaceholder(p) => term::app(
                "RPlaceholder",
                vec![
                    term::nat(p.universe.as_u32() as u64),
                    term::nat(p.bound.var.as_u32() as u64),
                ],
            ),
            ReStatic => term::atom("RStatic"),
            ReErased => term::atom("RErased"),
            ReError(_) => term::app("RError", vec![term::string("region error")]),
        }
    }

    pub fn tconst(&self, c: ty::Const<'tcx>) -> Term {
        match c.kind() {
            ConstKind::Param(p) => term::app(
                "CParam",
                vec![term::nat(p.index as u64), term::string(p.name.to_string())],
            ),
            ConstKind::Value(v) => {
                let t = self.ty(v.ty);
                match v
                    .valtree
                    .try_to_scalar()
                    .and_then(|s| s.try_to_scalar_int().ok())
                {
                    Some(s) => term::app("CValue", vec![t, term::int(s.to_int(s.size()))]),
                    None => term::app("CError", vec![term::string("non-scalar valtree")]),
                }
            }
            ConstKind::Unevaluated(u) => {
                let def_id = match u.kind {
                    UnevaluatedConstKind::Projection { def_id }
                    | UnevaluatedConstKind::Inherent { def_id }
                    | UnevaluatedConstKind::Free { def_id }
                    | UnevaluatedConstKind::Anon { def_id } => def_id,
                };
                term::app(
                    "CUnevaluated",
                    vec![self.path(def_id), self.generic_args(u.args)],
                )
            }
            ConstKind::Bound(depth, var) => term::app(
                "CBound",
                vec![bound_depth(depth), term::nat(var.var.as_u32() as u64)],
            ),
            ConstKind::Infer(_) => {
                term::app("CError", vec![term::string("infer const after typeck")])
            }
            ConstKind::Placeholder(p) => term::app(
                "CError",
                vec![term::string(format!("placeholder const {:?}", p))],
            ),
            ConstKind::Expr(_) => term::app("CError", vec![term::string("const expr")]),
            ConstKind::Error(_) => term::app("CError", vec![term::string("const error")]),
        }
    }

    pub fn generic_args(&self, args: ty::GenericArgsRef<'tcx>) -> Term {
        term::list(
            args.iter()
                .map(|a| match a.kind() {
                    ty::GenericArgKind::Type(t) => term::app("GTy", vec![self.ty(t)]),
                    ty::GenericArgKind::Lifetime(r) => term::app("GLifetime", vec![self.region(r)]),
                    ty::GenericArgKind::Const(c) => term::app("GConst", vec![self.tconst(c)]),
                })
                .collect(),
        )
    }

    fn fn_sig(
        &self,
        sig_tys: ty::Binder<'tcx, ty::FnSigTys<TyCtxt<'tcx>>>,
        hdr: ty::FnHeader<TyCtxt<'tcx>>,
    ) -> Term {
        let tys = sig_tys.skip_binder();
        let inputs: Vec<Term> = tys.inputs().iter().map(|t| self.ty(*t)).collect();
        term::app(
            "FnSig",
            vec![
                term::list(inputs),
                self.ty(tys.output()),
                term::boolean(hdr.c_variadic()),
                safety(hdr.safety()),
                term::string(format!("{:?}", hdr.abi())),
            ],
        )
    }

    fn dyn_preds(&self, preds: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>) -> Term {
        term::list(
            preds
                .iter()
                .map(|p| match p.skip_binder() {
                    ty::ExistentialPredicate::Trait(t) => term::app(
                        "DTrait",
                        vec![self.path(t.def_id), self.generic_args(t.args)],
                    ),
                    ty::ExistentialPredicate::Projection(p) => term::app(
                        "DProjection",
                        vec![
                            self.path(p.def_id),
                            self.generic_args(p.args),
                            match p.term.kind() {
                                ty::TermKind::Ty(t) => self.ty(t),
                                ty::TermKind::Const(c) => {
                                    term::app("TError", vec![term::string(self.tconst(c).render())])
                                }
                            },
                        ],
                    ),
                    ty::ExistentialPredicate::AutoTrait(def_id) => {
                        term::app("DAutoTrait", vec![self.path(def_id)])
                    }
                })
                .collect(),
        )
    }
}

fn error(msg: &str) -> Term {
    term::app("TError", vec![term::string(msg)])
}

fn int_width(i: ty::IntTy) -> Term {
    term::atom(match i {
        ty::IntTy::Isize => "WSize",
        ty::IntTy::I8 => "W8",
        ty::IntTy::I16 => "W16",
        ty::IntTy::I32 => "W32",
        ty::IntTy::I64 => "W64",
        ty::IntTy::I128 => "W128",
    })
}

fn uint_width(u: ty::UintTy) -> Term {
    term::atom(match u {
        ty::UintTy::Usize => "WSize",
        ty::UintTy::U8 => "W8",
        ty::UintTy::U16 => "W16",
        ty::UintTy::U32 => "W32",
        ty::UintTy::U64 => "W64",
        ty::UintTy::U128 => "W128",
    })
}

fn float_width(f: ty::FloatTy) -> Term {
    term::atom(match f {
        ty::FloatTy::F16 => "FW16",
        ty::FloatTy::F32 => "FW32",
        ty::FloatTy::F64 => "FW64",
        ty::FloatTy::F128 => "FW128",
    })
}

pub fn mutability(m: rustc_middle::mir::Mutability) -> Term {
    term::atom(match m {
        rustc_middle::mir::Mutability::Mut => "Mut",
        rustc_middle::mir::Mutability::Not => "Imm",
    })
}

fn safety(s: rustc_hir::Safety) -> Term {
    term::atom(match s {
        rustc_hir::Safety::Safe => "Safe",
        rustc_hir::Safety::Unsafe => "Unsafe",
    })
}

fn alias_kind(k: ty::AliasTyKind) -> Term {
    term::atom(match k {
        ty::AliasTyKind::Projection { .. } => "AkProjection",
        ty::AliasTyKind::Inherent { .. } => "AkInherent",
        ty::AliasTyKind::Opaque { .. } => "AkOpaque",
        ty::AliasTyKind::Free { .. } => "AkFree",
    })
}

fn bound_depth(d: rustc_type_ir::BoundVarIndexKind) -> Term {
    match d {
        rustc_type_ir::BoundVarIndexKind::Bound(i) => {
            term::app("BdIndex", vec![term::nat(i.as_u32() as u64)])
        }
        rustc_type_ir::BoundVarIndexKind::Canonical => term::atom("BdCanonical"),
    }
}

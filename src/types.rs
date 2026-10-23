use rustc_hir::Safety;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_type_ir::{BoundVarIndexKind, ConstKind, RegionKind, TyKind, UnevaluatedConstKind};

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
                let adt_id = def.did();
                self.record_adt(adt_id);
                term::app("TAdt", vec![self.path(adt_id), self.generic_args(args)])
            }
            Foreign(def_id) => term::app("TForeign", vec![self.path(*def_id)]),
            Str => term::atom("TStr"),
            Array(elem, len) => term::app("TArray", vec![self.ty(*elem), self.type_const(*len)]),
            Pat(base, pat) => term::app("TPat", vec![self.ty(*base), self.pattern(*pat)]),
            Slice(elem) => term::app("TSlice", vec![self.ty(*elem)]),
            RawPtr(pointee, m) => term::app("TRawPtr", vec![self.ty(*pointee), mutability(*m)]),
            Ref(r, pointee, m) => term::app(
                "TRef",
                vec![self.region(*r), self.ty(*pointee), mutability(*m)],
            ),
            FnDef(def_id, args) => {
                term::app("TFnDef", vec![self.path(*def_id), self.generic_args(args)])
            }
            FnPtr(signature, header) => {
                term::app("TFnPtr", vec![self.fn_signature(*signature, *header)])
            }
            UnsafeBinder(b) => term::app("TUnsafeBinder", vec![self.ty(b.skip_binder())]),
            Dynamic(preds, r) => term::app(
                "TDynamic",
                vec![self.dyn_predicates(preds), self.region(*r)],
            ),
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

    fn pattern(&self, pat: ty::Pattern<'tcx>) -> Term {
        match &*pat {
            ty::PatternKind::Range { start, end } => term::app(
                "PatRange",
                vec![self.type_const(*start), self.type_const(*end)],
            ),
            ty::PatternKind::Or(alts) => term::app(
                "PatOr",
                vec![term::list(alts.iter().map(|p| self.pattern(p)).collect())],
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

    pub fn type_const(&self, c: ty::Const<'tcx>) -> Term {
        use rustc_middle::ty::ValTreeKindExt as _;

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
                    ty::GenericArgKind::Const(c) => term::app("GConst", vec![self.type_const(c)]),
                })
                .collect(),
        )
    }

    fn fn_signature(
        &self,
        signature: ty::Binder<'tcx, ty::FnSigTys<TyCtxt<'tcx>>>,
        header: ty::FnHeader<TyCtxt<'tcx>>,
    ) -> Term {
        let signature_types = signature.skip_binder();
        let inputs: Vec<Term> = signature_types
            .inputs()
            .iter()
            .map(|t| self.ty(*t))
            .collect();
        term::app(
            "FnSig",
            vec![
                term::list(inputs),
                self.ty(signature_types.output()),
                term::boolean(header.c_variadic()),
                safety(header.safety()),
                term::string(format!("{:?}", header.abi())),
            ],
        )
    }

    fn dyn_predicates(&self, preds: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>) -> Term {
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
                                ty::TermKind::Const(c) => term::app(
                                    "TError",
                                    vec![term::string(self.type_const(c).render())],
                                ),
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

fn error(message: &str) -> Term {
    term::app("TError", vec![term::string(message)])
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

pub fn mutability(m: Mutability) -> Term {
    term::atom(match m {
        Mutability::Mut => "Mut",
        Mutability::Not => "Imm",
    })
}

pub fn safety(s: Safety) -> Term {
    term::atom(match s {
        Safety::Safe => "Safe",
        Safety::Unsafe => "Unsafe",
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

fn bound_depth(d: BoundVarIndexKind) -> Term {
    match d {
        BoundVarIndexKind::Bound(i) => term::app("BdIndex", vec![term::nat(i.as_u32() as u64)]),
        BoundVarIndexKind::Canonical => term::atom("BdCanonical"),
    }
}

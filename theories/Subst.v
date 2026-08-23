From RustRocq Require Import Syntax.
From Stdlib Require Import String List.
Import ListNotations.

Local Open Scope string_scope.

Definition kind_mismatch : name := "generic argument kind mismatch".

Definition subst_region (args : list garg) (r : region) : region :=
  match r with
  | RParam i nm =>
      match nth_error args i with
      | Some (GLifetime r') => r'
      | Some _ => RError kind_mismatch
      | None => RParam i nm
      end
  | _ => r
  end.

Fixpoint subst_ty (args : list garg) (t : ty) {struct t} : ty :=
  let fix gargs (l : list garg) : list garg :=
    match l with [] => [] | x :: r => subst_garg args x :: gargs r end in
  let fix tys (l : list ty) : list ty :=
    match l with [] => [] | x :: r => subst_ty args x :: tys r end in
  let fix dps (l : list dyn_pred) : list dyn_pred :=
    match l with [] => [] | x :: r => subst_dyn_pred args x :: dps r end in
  match t with
  | TBool | TChar | TStr | TNever => t
  | TInt _ | TUint _ | TFloat _ => t
  | TForeign _ | TBound _ _ | TPlaceholder _ _ | TError _ => t
  | TParam i nm =>
      match nth_error args i with
      | Some (GTy t') => t'
      | Some _ => TError kind_mismatch
      | None => t
      end
  | TAdt p a => TAdt p (gargs a)
  | TArray e n => TArray (subst_ty args e) (subst_tconst args n)
  | TPat b p => TPat (subst_ty args b) (subst_ty_pat args p)
  | TSlice e => TSlice (subst_ty args e)
  | TRawPtr p m => TRawPtr (subst_ty args p) m
  | TRef r p m => TRef (subst_region args r) (subst_ty args p) m
  | TFnDef p a => TFnDef p (gargs a)
  | TFnPtr s => TFnPtr (subst_fn_sig args s)
  | TUnsafeBinder i => TUnsafeBinder (subst_ty args i)
  | TDynamic ps r => TDynamic (dps ps) (subst_region args r)
  | TClosure p a => TClosure p (gargs a)
  | TCoroutineClosure p a => TCoroutineClosure p (gargs a)
  | TCoroutine p a => TCoroutine p (gargs a)
  | TCoroutineWitness p a => TCoroutineWitness p (gargs a)
  | TTuple es => TTuple (tys es)
  | TAlias k p a => TAlias k p (gargs a)
  end

with subst_tconst (args : list garg) (c : tconst) {struct c} : tconst :=
  let fix gargs (l : list garg) : list garg :=
    match l with [] => [] | x :: r => subst_garg args x :: gargs r end in
  match c with
  | CParam i nm =>
      match nth_error args i with
      | Some (GConst c') => c'
      | Some _ => CError kind_mismatch
      | None => c
      end
  | CValue t bits => CValue (subst_ty args t) bits
  | CUnevaluated p a => CUnevaluated p (gargs a)
  | CBound _ _ | CError _ => c
  end

with subst_garg (args : list garg) (g : garg) {struct g} : garg :=
  match g with
  | GTy t => GTy (subst_ty args t)
  | GLifetime r => GLifetime (subst_region args r)
  | GConst c => GConst (subst_tconst args c)
  end

with subst_fn_sig (args : list garg) (s : fn_sig) {struct s} : fn_sig :=
  let fix tys (l : list ty) : list ty :=
    match l with [] => [] | x :: r => subst_ty args x :: tys r end in
  match s with
  | FnSig ins out variadic sf abi =>
      FnSig (tys ins) (subst_ty args out) variadic sf abi
  end

with subst_dyn_pred (args : list garg) (d : dyn_pred) {struct d} : dyn_pred :=
  let fix gargs (l : list garg) : list garg :=
    match l with [] => [] | x :: r => subst_garg args x :: gargs r end in
  match d with
  | DTrait p a => DTrait p (gargs a)
  | DProjection p a t => DProjection p (gargs a) (subst_ty args t)
  | DAutoTrait p => DAutoTrait p
  end

with subst_ty_pat (args : list garg) (p : ty_pat) {struct p} : ty_pat :=
  let fix pats (l : list ty_pat) : list ty_pat :=
    match l with [] => [] | x :: r => subst_ty_pat args x :: pats r end in
  match p with
  | PatRange lo hi => PatRange (subst_tconst args lo) (subst_tconst args hi)
  | PatOr alts => PatOr (pats alts)
  end.

Definition subst_tys (args : list garg) : list ty -> list ty := map (subst_ty args).
Definition subst_gargs (args : list garg) : list garg -> list garg := map (subst_garg args).

Definition subst_bound (args : list garg) (b : bound) : bound :=
  match b with
  | BdTrait p a => BdTrait p (subst_gargs args a)
  | BdProjection p a t => BdProjection p (subst_gargs args a) (subst_ty args t)
  | BdOutlives x y => BdOutlives (subst_region args x) (subst_region args y)
  | BdTyOutlives t r => BdTyOutlives (subst_ty args t) (subst_region args r)
  | BdConstArgHasType c t => BdConstArgHasType (subst_tconst args c) (subst_ty args t)
  | BdWellFormedTy t => BdWellFormedTy (subst_ty args t)
  | BdWellFormedConst c => BdWellFormedConst (subst_tconst args c)
  | BdConstEvaluatable c => BdConstEvaluatable (subst_tconst args c)
  | BdHostEffect p a k => BdHostEffect p (subst_gargs args a) k
  | BdUnstableFeature f => BdUnstableFeature f
  end.

Definition subst_proj_elem (args : list garg) (e : proj_elem) : proj_elem :=
  match e with
  | PField i t => PField i (subst_ty args t)
  | POpaqueCast t => POpaqueCast (subst_ty args t)
  | PUnwrapUnsafeBinder t => PUnwrapUnsafeBinder (subst_ty args t)
  | PDeref | PIndex _ => e
  | PConstantIndex _ _ _ | PSubslice _ _ _ | PDowncast _ _ => e
  end.

Definition subst_place (args : list garg) (p : place) : place :=
  Place (pl_local p) (map (subst_proj_elem args) (pl_proj p)).

Definition subst_constant (args : list garg) (c : constant) : constant :=
  match c with
  | KTy t k => KTy (subst_ty args t) (subst_tconst args k)
  | KUnevaluated p a pr t =>
      KUnevaluated p (subst_gargs args a) pr (subst_ty args t)
  | KVal v t => KVal v (subst_ty args t)
  end.

Definition subst_const_op (args : list garg) (c : const_op) : const_op :=
  ConstOp (co_span c) (subst_constant args (co_const c)).

Definition subst_operand (args : list garg) (o : operand) : operand :=
  match o with
  | OCopy p => OCopy (subst_place args p)
  | OMove p => OMove (subst_place args p)
  | OConst c => OConst (subst_const_op args c)
  | ORuntimeCheck c => ORuntimeCheck c
  end.

Definition subst_aggregate_kind (args : list garg) (k : aggregate_kind) : aggregate_kind :=
  match k with
  | AgArray e => AgArray (subst_ty args e)
  | AgTuple => AgTuple
  | AgAdt p v a f => AgAdt p v (subst_gargs args a) f
  | AgClosure p a => AgClosure p (subst_gargs args a)
  | AgCoroutine p a => AgCoroutine p (subst_gargs args a)
  | AgCoroutineClosure p a => AgCoroutineClosure p (subst_gargs args a)
  | AgRawPtr t m => AgRawPtr (subst_ty args t) m
  end.

Definition subst_rvalue (args : list garg) (r : rvalue) : rvalue :=
  match r with
  | RUse o rt => RUse (subst_operand args o) rt
  | RRepeat o n => RRepeat (subst_operand args o) (subst_tconst args n)
  | RRef rg bk p => RRef (subst_region args rg) bk (subst_place args p)
  | RThreadLocalRef p => RThreadLocalRef p
  | RRawPtr k p => RRawPtr k (subst_place args p)
  | RCast k o t => RCast k (subst_operand args o) (subst_ty args t)
  | RBinaryOp op l r' => RBinaryOp op (subst_operand args l) (subst_operand args r')
  | RUnaryOp op o => RUnaryOp op (subst_operand args o)
  | RDiscriminant p => RDiscriminant (subst_place args p)
  | RAggregate k fs =>
      RAggregate (subst_aggregate_kind args k) (map (subst_operand args) fs)
  | RCopyForDeref p => RCopyForDeref (subst_place args p)
  | RWrapUnsafeBinder o t => RWrapUnsafeBinder (subst_operand args o) (subst_ty args t)
  | RReborrow t m p => RReborrow (subst_ty args t) m (subst_place args p)
  end.

Definition subst_nd_intrinsic (args : list garg) (i : nd_intrinsic) : nd_intrinsic :=
  match i with
  | NiAssume o => NiAssume (subst_operand args o)
  | NiCopyNonOverlapping s d c =>
      NiCopyNonOverlapping (subst_operand args s) (subst_operand args d)
        (subst_operand args c)
  end.

Definition subst_statement_kind (args : list garg) (k : statement_kind) : statement_kind :=
  match k with
  | SAssign p r => SAssign (subst_place args p) (subst_rvalue args r)
  | SFakeRead c p => SFakeRead c (subst_place args p)
  | SSetDiscriminant p v => SSetDiscriminant (subst_place args p) v
  | SStorageLive l => SStorageLive l
  | SStorageDead l => SStorageDead l
  | SPlaceMention p => SPlaceMention (subst_place args p)
  | SAscribeUserType p u v => SAscribeUserType (subst_place args p) u v
  | SCoverage k' => SCoverage k'
  | SIntrinsic i => SIntrinsic (subst_nd_intrinsic args i)
  | SConstEvalCounter => SConstEvalCounter
  | SNop => SNop
  | SBackwardIncompatibleDropHint p r =>
      SBackwardIncompatibleDropHint (subst_place args p) r
  end.

Definition subst_statement (args : list garg) (s : statement) : statement :=
  Stmt (st_span s) (subst_statement_kind args (st_kind s)).

Definition subst_assert_kind (args : list garg) (k : assert_kind) : assert_kind :=
  match k with
  | AsBoundsCheck l i => AsBoundsCheck (subst_operand args l) (subst_operand args i)
  | AsOverflow op l r => AsOverflow op (subst_operand args l) (subst_operand args r)
  | AsOverflowNeg o => AsOverflowNeg (subst_operand args o)
  | AsDivisionByZero o => AsDivisionByZero (subst_operand args o)
  | AsRemainderByZero o => AsRemainderByZero (subst_operand args o)
  | AsResumedAfterReturn k' => AsResumedAfterReturn k'
  | AsResumedAfterPanic k' => AsResumedAfterPanic k'
  | AsResumedAfterDrop k' => AsResumedAfterDrop k'
  | AsMisalignedPointerDereference r f =>
      AsMisalignedPointerDereference (subst_operand args r) (subst_operand args f)
  | AsNullPointerDereference => AsNullPointerDereference
  | AsInvalidEnumConstruction o => AsInvalidEnumConstruction (subst_operand args o)
  end.

Definition subst_asm_operand (args : list garg) (o : asm_operand) : asm_operand :=
  match o with
  | AoIn r v => AoIn r (subst_operand args v)
  | AoOut r l p => AoOut r l (option_map (subst_place args) p)
  | AoInOut r l v p =>
      AoInOut r l (subst_operand args v) (option_map (subst_place args) p)
  | AoConst v => AoConst (subst_const_op args v)
  | AoSymFn v => AoSymFn (subst_const_op args v)
  | AoSymStatic p => AoSymStatic p
  | AoLabel i => AoLabel i
  end.

Definition subst_terminator_kind (args : list garg) (k : terminator_kind) : terminator_kind :=
  match k with
  | TGoto t => TGoto t
  | TSwitchInt d ts o => TSwitchInt (subst_operand args d) ts o
  | TUnwindResume => TUnwindResume
  | TUnwindTerminate r => TUnwindTerminate r
  | TReturn => TReturn
  | TUnreachable => TUnreachable
  | TDrop p t u rp ad => TDrop (subst_place args p) t u rp ad
  | TCall f as' d t u s sp =>
      TCall (subst_operand args f) (map (subst_operand args) as')
        (subst_place args d) t u s sp
  | TTailCall f as' sp =>
      TTailCall (subst_operand args f) (map (subst_operand args) as') sp
  | TAssert c e m t u =>
      TAssert (subst_operand args c) e (subst_assert_kind args m) t u
  | TYield v r ra d => TYield (subst_operand args v) r (subst_place args ra) d
  | TCoroutineDrop => TCoroutineDrop
  | TFalseEdge r i => TFalseEdge r i
  | TFalseUnwind r u => TFalseUnwind r u
  | TInlineAsm m tp os opt ts u =>
      TInlineAsm m tp (map (subst_asm_operand args) os) opt ts u
  end.

Definition subst_terminator (args : list garg) (t : terminator) : terminator :=
  Term (tm_span t) (subst_terminator_kind args (tm_kind t)).

Definition subst_block (args : list garg) (b : basic_block) : basic_block :=
  BasicBlock (bb_id b)
    (map (subst_statement args) (bb_stmts b))
    (subst_terminator args (bb_term b))
    (bb_is_cleanup b).

Definition subst_local_decl (args : list garg) (d : local_decl) : local_decl :=
  LocalDecl (subst_ty args (ld_ty d)) (ld_mut d) (ld_name d) (ld_span d).

Definition subst_body (args : list garg) (b : body) : body :=
  Body (bd_name b) (bd_file b) (bd_span b)
    (skipn (length args) (bd_generics b))
    (map (subst_bound args) (bd_bounds b))
    (bd_arg_count b)
    (map (subst_local_decl args) (bd_locals b))
    (map (subst_block args) (bd_blocks b))
    (bd_regions b)
    (bd_borrowck b).

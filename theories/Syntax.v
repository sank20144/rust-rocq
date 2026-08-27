From Stdlib Require Import String List ZArith.

Local Open Scope string_scope.

Definition name := string.

Definition local := nat.
Definition block_id := nat.
Definition field := nat.
Definition variant := nat.

Inductive span :=
  | Span (lo_line lo_col hi_line hi_col : nat)
  | SpanIn (file : name) (lo_line lo_col hi_line hi_col : nat)
  | NoSpan.

Inductive int_width := W8 | W16 | W32 | W64 | W128 | WSize.
Inductive float_width := FW16 | FW32 | FW64 | FW128.
Inductive mutability := Mut | Imm.
Inductive safety := Safe | Unsafe.

Inductive bound_depth := BdIndex (n : nat) | BdCanonical.

Inductive region :=
  | RVar (n : nat)
  | RParam (idx : nat) (nm : name)
  | RBound (depth : bound_depth) (idx : nat)
  | RPlaceholder (univ : nat) (idx : nat)
  | RStatic
  | RErased
  | RError (msg : name).

Inductive alias_kind := AkProjection | AkInherent | AkOpaque | AkFree.

Inductive ty :=
  | TBool
  | TChar
  | TInt (w : int_width)
  | TUint (w : int_width)
  | TFloat (w : float_width)
  | TAdt (path : name) (args : list garg)
  | TForeign (path : name)
  | TStr
  | TArray (elem : ty) (len : tconst)
  | TPat (base : ty) (pat : ty_pat)
  | TSlice (elem : ty)
  | TRawPtr (pointee : ty) (m : mutability)
  | TRef (r : region) (pointee : ty) (m : mutability)
  | TFnDef (path : name) (args : list garg)
  | TFnPtr (sig : fn_sig)
  | TUnsafeBinder (inner : ty)
  | TDynamic (preds : list dyn_pred) (r : region)
  | TClosure (path : name) (args : list garg)
  | TCoroutineClosure (path : name) (args : list garg)
  | TCoroutine (path : name) (args : list garg)
  | TCoroutineWitness (path : name) (args : list garg)
  | TNever
  | TTuple (elems : list ty)
  | TAlias (k : alias_kind) (path : name) (args : list garg)
  | TParam (idx : nat) (nm : name)
  | TBound (depth : bound_depth) (idx : nat)
  | TPlaceholder (univ : nat) (idx : nat)
  | TError (msg : name)

with tconst :=
  | CParam (idx : nat) (nm : name)
  | CValue (t : ty) (bits : Z)
  | CUnevaluated (path : name) (args : list garg)
  | CBound (depth : bound_depth) (idx : nat)
  | CError (msg : name)

with garg :=
  | GTy (t : ty)
  | GLifetime (r : region)
  | GConst (c : tconst)

with fn_sig :=
  | FnSig (inputs : list ty) (output : ty) (variadic : bool) (sf : safety) (abi : name)

with dyn_pred :=
  | DTrait (path : name) (args : list garg)
  | DProjection (path : name) (args : list garg) (t : ty)
  | DAutoTrait (path : name)

with ty_pat :=
  | PatRange (lo hi : tconst)
  | PatOr (alts : list ty_pat).

Inductive proj_elem :=
  | PDeref
  | PField (idx : field) (t : ty)
  | PIndex (l : local)
  | PConstantIndex (offset : nat) (min_length : nat) (from_end : bool)
  | PSubslice (from_ : nat) (to_ : nat) (from_end : bool)
  | PDowncast (nm : option name) (v : variant)
  | POpaqueCast (t : ty)
  | PUnwrapUnsafeBinder (t : ty).

Record place := Place {
  pl_local : local;
  pl_proj : list proj_elem;
}.

Inductive scalar :=
  | ScInt (bits : Z) (size_bytes : nat)
  | ScPtr (alloc : name) (offset : Z) (size_bytes : nat).

Inductive const_value :=
  | CvScalar (s : scalar)
  | CvZeroSized
  | CvSlice (alloc : name) (meta : Z)
  | CvIndirect (alloc : name) (offset : Z).

Inductive constant :=
  | KTy (t : ty) (c : tconst)
  | KUnevaluated (path : name) (args : list garg) (promoted : option nat) (t : ty)
  | KVal (v : const_value) (t : ty).

Record const_op := ConstOp {
  co_span : span;
  co_const : constant;
}.

Inductive runtime_check := RcUbChecks | RcContractChecks | RcOverflowChecks.

Inductive operand :=
  | OCopy (p : place)
  | OMove (p : place)
  | OConst (c : const_op)
  | ORuntimeCheck (c : runtime_check).

Inductive fake_borrow_kind := FbShallow | FbDeep.
Inductive mut_borrow_kind := MbDefault | MbTwoPhase | MbClosureCapture.

Inductive borrow_kind :=
  | BkShared
  | BkFake (k : fake_borrow_kind)
  | BkMut (k : mut_borrow_kind).

Inductive raw_ptr_kind := RpMut | RpConst | RpFakeForPtrMetadata.

Inductive coercion_source := CoAsCast | CoImplicit.

Inductive pointer_coercion :=
  | PcReifyFnPointer (sf : safety)
  | PcUnsafeFnPointer
  | PcClosureFnPointer (sf : safety)
  | PcMutToConstPointer
  | PcArrayToPointer
  | PcUnsize.

Inductive cast_kind :=
  | CkPointerExposeProvenance
  | CkPointerWithExposedProvenance
  | CkPointerCoercion (pc : pointer_coercion) (src : coercion_source)
  | CkIntToInt
  | CkFloatToInt
  | CkFloatToFloat
  | CkIntToFloat
  | CkPtrToPtr
  | CkFnPtrToPtr
  | CkTransmute
  | CkSubtype.

Inductive bin_op :=
  | BAdd | BAddUnchecked | BAddWithOverflow
  | BSub | BSubUnchecked | BSubWithOverflow
  | BMul | BMulUnchecked | BMulWithOverflow
  | BDiv | BRem
  | BBitXor | BBitAnd | BBitOr
  | BShl | BShlUnchecked | BShr | BShrUnchecked
  | BEq | BLt | BLe | BNe | BGe | BGt
  | BCmp | BOffset.

Inductive un_op := UNot | UNeg | UPtrMetadata.

Inductive aggregate_kind :=
  | AgArray (elem : ty)
  | AgTuple
  | AgAdt (path : name) (v : variant) (args : list garg) (active_field : option field)
  | AgClosure (path : name) (args : list garg)
  | AgCoroutine (path : name) (args : list garg)
  | AgCoroutineClosure (path : name) (args : list garg)
  | AgRawPtr (pointee : ty) (m : mutability).

Inductive with_retag := RetagYes | RetagNo.

Inductive rvalue :=
  | RUse (o : operand) (rt : with_retag)
  | RRepeat (o : operand) (n : tconst)
  | RRef (r : region) (bk : borrow_kind) (p : place)
  | RThreadLocalRef (path : name)
  | RRawPtr (k : raw_ptr_kind) (p : place)
  | RCast (k : cast_kind) (o : operand) (t : ty)
  | RBinaryOp (op : bin_op) (l : operand) (r : operand)
  | RUnaryOp (op : un_op) (o : operand)
  | RDiscriminant (p : place)
  | RAggregate (k : aggregate_kind) (fields : list operand)
  | RCopyForDeref (p : place)
  | RWrapUnsafeBinder (o : operand) (t : ty)
  | RReborrow (t : ty) (m : mutability) (p : place).

Inductive fake_read_cause :=
  | FrMatchGuard
  | FrMatchedPlace (d : option name)
  | FrGuardBinding
  | FrLet (d : option name)
  | FrIndex.

Inductive variance := VCovariant | VInvariant | VContravariant | VBivariant.

Inductive nd_intrinsic :=
  | NiAssume (o : operand)
  | NiCopyNonOverlapping (src : operand) (dst : operand) (count : operand).

Inductive statement_kind :=
  | SAssign (p : place) (r : rvalue)
  | SFakeRead (c : fake_read_cause) (p : place)
  | SSetDiscriminant (p : place) (v : variant)
  | SStorageLive (l : local)
  | SStorageDead (l : local)
  | SPlaceMention (p : place)
  | SAscribeUserType (p : place) (uty : name) (vr : variance)
  | SCoverage (kind : name)
  | SIntrinsic (i : nd_intrinsic)
  | SConstEvalCounter
  | SNop
  | SBackwardIncompatibleDropHint (p : place) (reason : name).

Record statement := Stmt {
  st_span : span;
  st_kind : statement_kind;
}.

Inductive unwind_terminate_reason := UtAbi | UtInCleanup.

Inductive unwind_action :=
  | UaContinue
  | UaUnreachable
  | UaTerminate (r : unwind_terminate_reason)
  | UaCleanup (b : block_id).

Inductive assert_kind :=
  | AsBoundsCheck (len : operand) (index : operand)
  | AsOverflow (op : bin_op) (l : operand) (r : operand)
  | AsOverflowNeg (o : operand)
  | AsDivisionByZero (o : operand)
  | AsRemainderByZero (o : operand)
  | AsResumedAfterReturn (k : name)
  | AsResumedAfterPanic (k : name)
  | AsResumedAfterDrop (k : name)
  | AsMisalignedPointerDereference (required : operand) (found : operand)
  | AsNullPointerDereference
  | AsInvalidEnumConstruction (o : operand).

Inductive call_source :=
  | SrcOverloadedOperator
  | SrcMatchCmp
  | SrcMisc
  | SrcUse
  | SrcNormal.

Inductive asm_macro := AmAsm | AmNakedAsm.

Inductive asm_operand :=
  | AoIn (reg : name) (value : operand)
  | AoOut (reg : name) (late : bool) (p : option place)
  | AoInOut (reg : name) (late : bool) (in_value : operand) (out_place : option place)
  | AoConst (value : const_op)
  | AoSymFn (value : const_op)
  | AoSymStatic (path : name)
  | AoLabel (target_index : nat).

Inductive terminator_kind :=
  | TGoto (target : block_id)
  | TSwitchInt (discr : operand) (targets : list (Z * block_id)) (otherwise : block_id)
  | TUnwindResume
  | TUnwindTerminate (r : unwind_terminate_reason)
  | TReturn
  | TUnreachable
  | TDrop (p : place) (target : block_id) (unwind : unwind_action)
          (replace : bool) (async_drop : option block_id)
  | TCall (func : operand) (args : list operand) (dest : place)
          (target : option block_id) (unwind : unwind_action)
          (src : call_source) (fn_span : span)
  | TTailCall (func : operand) (args : list operand) (fn_span : span)
  | TAssert (cond : operand) (expected : bool) (msg : assert_kind)
            (target : block_id) (unwind : unwind_action)
  | TYield (value : operand) (resume : block_id) (resume_arg : place)
           (drop : option block_id)
  | TCoroutineDrop
  | TFalseEdge (real : block_id) (imaginary : block_id)
  | TFalseUnwind (real : block_id) (unwind : unwind_action)
  | TInlineAsm (macro : asm_macro) (template : list name)
               (operands : list asm_operand) (options : list name)
               (targets : list block_id) (unwind : unwind_action).

Record terminator := Term {
  tm_span : span;
  tm_kind : terminator_kind;
}.

Record basic_block := BasicBlock {
  bb_id : block_id;
  bb_stmts : list statement;
  bb_term : terminator;
  bb_is_cleanup : bool;
}.

Record local_decl := LocalDecl {
  ld_ty : ty;
  ld_mut : mutability;
  ld_name : option name;
  ld_span : span;
}.

Inductive generic_param :=
  | GpTy (idx : nat) (nm : name)
  | GpLifetime (idx : nat) (nm : name)
  | GpConst (idx : nat) (nm : name) (t : ty).

Inductive bound :=
  | BdTrait (path : name) (args : list garg)
  | BdProjection (path : name) (args : list garg) (t : ty)
  | BdOutlives (a : region) (b : region)
  | BdTyOutlives (t : ty) (r : region)
  | BdConstArgHasType (c : tconst) (t : ty)
  | BdWellFormedTy (t : ty)
  | BdWellFormedConst (c : tconst)
  | BdConstEvaluatable (c : tconst)
  | BdHostEffect (path : name) (args : list garg) (constness : name)
  | BdUnstableFeature (feature : name).

Inductive assoc_kind :=
  | AiFn (has_self : bool)
  | AiConst
  | AiType.

Record assoc_item := AssocItem {
  ai_name : name;
  ai_path : name;
  ai_kind : assoc_kind;
  ai_has_default : bool;
}.

Record trait_def := TraitDef {
  tr_path : name;
  tr_generics : list generic_param;
  tr_bounds : list bound;
  tr_items : list assoc_item;
}.

Record impl_def := ImplDef {
  ip_path : name;
  ip_trait : name;
  ip_args : list garg;
  ip_generics : list generic_param;
  ip_bounds : list bound;
  ip_items : list (name * name);
  ip_negative : bool;
}.

Inductive adt_kind := AkStruct | AkEnum | AkUnion.

Record variant_def := VariantDef {
  vd_name : name;
  vd_index : variant;
  vd_fields : list (name * ty);
}.

Record adt_def := AdtDef {
  ad_path : name;
  ad_kind : adt_kind;
  ad_generics : list generic_param;
  ad_variants : list variant_def;
  ad_repr : list name;
}.

Definition origin := nat.
Definition loan := nat.

Inductive point :=
  | PtStart (b : block_id) (stmt : nat)
  | PtMid (b : block_id) (stmt : nat).

Record loan_start := LoanStart {
  ls_origin : origin;
  ls_loan : loan;
  ls_at : point;
}.

Record loan_end := LoanEnd {
  le_loan : loan;
  le_from : point;
  le_to : option point;
}.

Record borrowck_annotations := BorrowckAnnotations {
  ba_universal_regions : list origin;
  ba_placeholders : list (origin * loan);
  ba_known_placeholder_subsets : list (origin * origin);
  ba_loan_starts : list loan_start;
  ba_loan_ends : list loan_end;
}.

Record body := Body {
  bd_name : name;
  bd_file : name;
  bd_span : span;
  bd_generics : list generic_param;
  bd_bounds : list bound;
  bd_arg_count : nat;
  bd_locals : list local_decl;
  bd_blocks : list basic_block;
  bd_regions : list origin;
  bd_borrowck : borrowck_annotations;
}.

Definition int_width_eqb (a b : int_width) : bool :=
  match a, b with
  | W8, W8 | W16, W16 | W32, W32 | W64, W64 | W128, W128 | WSize, WSize => true
  | _, _ => false
  end.

Definition float_width_eqb (a b : float_width) : bool :=
  match a, b with
  | FW16, FW16 | FW32, FW32 | FW64, FW64 | FW128, FW128 => true
  | _, _ => false
  end.

Definition mutability_eqb (a b : mutability) : bool :=
  match a, b with Mut, Mut | Imm, Imm => true | _, _ => false end.

Definition alias_kind_eqb (a b : alias_kind) : bool :=
  match a, b with
  | AkProjection, AkProjection | AkInherent, AkInherent
  | AkOpaque, AkOpaque | AkFree, AkFree => true
  | _, _ => false
  end.

Fixpoint ty_eqb (a b : ty) {struct a} : bool :=
  let fix gargs (xs ys : list garg) : bool :=
    match xs, ys with
    | nil, nil => true
    | cons x xs, cons y ys => andb (garg_eqb x y) (gargs xs ys)
    | _, _ => false
    end in
  let fix tys (xs ys : list ty) : bool :=
    match xs, ys with
    | nil, nil => true
    | cons x xs, cons y ys => andb (ty_eqb x y) (tys xs ys)
    | _, _ => false
    end in
  match a, b with
  | TBool, TBool | TChar, TChar | TStr, TStr | TNever, TNever => true
  | TInt x, TInt y | TUint x, TUint y => int_width_eqb x y
  | TFloat x, TFloat y => float_width_eqb x y
  | TAdt p x, TAdt q y => andb (String.eqb p q) (gargs x y)
  | TForeign p, TForeign q => String.eqb p q
  | TArray e n, TArray f m => andb (ty_eqb e f) (tconst_eqb n m)
  | TSlice e, TSlice f => ty_eqb e f
  | TRawPtr p x, TRawPtr q y => andb (ty_eqb p q) (mutability_eqb x y)
  | TRef _ p x, TRef _ q y => andb (ty_eqb p q) (mutability_eqb x y)
  | TFnDef p x, TFnDef q y => andb (String.eqb p q) (gargs x y)
  | TUnsafeBinder x, TUnsafeBinder y => ty_eqb x y
  | TClosure p x, TClosure q y => andb (String.eqb p q) (gargs x y)
  | TCoroutine p x, TCoroutine q y => andb (String.eqb p q) (gargs x y)
  | TCoroutineClosure p x, TCoroutineClosure q y => andb (String.eqb p q) (gargs x y)
  | TCoroutineWitness p x, TCoroutineWitness q y => andb (String.eqb p q) (gargs x y)
  | TTuple x, TTuple y => tys x y
  | TAlias k p x, TAlias l q y =>
      andb (alias_kind_eqb k l) (andb (String.eqb p q) (gargs x y))
  | TParam i _, TParam j _ => Nat.eqb i j
  | TError x, TError y => String.eqb x y
  | _, _ => false
  end

with tconst_eqb (a b : tconst) {struct a} : bool :=
  match a, b with
  | CParam i _, CParam j _ => Nat.eqb i j
  | CValue t x, CValue u y => andb (ty_eqb t u) (Z.eqb x y)
  | CError x, CError y => String.eqb x y
  | _, _ => false
  end

with garg_eqb (a b : garg) {struct a} : bool :=
  match a, b with
  | GTy x, GTy y => ty_eqb x y
  | GLifetime _, GLifetime _ => true
  | GConst x, GConst y => tconst_eqb x y
  | _, _ => false
  end.

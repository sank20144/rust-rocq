From RustRocq Require Import Syntax Layout Memory Subst LayoutAlg.
From Stdlib Require Import String List ZArith Lia.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition bounded (A : Type) : Type := nat -> option A.

Definition Terminates {A} (d : bounded A) (a : A) : Prop := exists n, d n = Some a.

Definition Diverges {A} (d : bounded A) : Prop := forall n, d n = None.

Definition Monotone {A} (d : bounded A) : Prop :=
  forall n m a, n <= m -> d n = Some a -> d m = Some a.

Inductive outcome (A : Type) :=
  | Ok (a : A) (st : prog_state)
  | Ub (reason : ub_reason)
  | Unmodelled (what : string)
  | Mismatch (what : string).

Arguments Ok {A} _ _.
Arguments Ub {A} _.
Arguments Unmodelled {A} _.
Arguments Mismatch {A} _.

Definition M (A : Type) : Type := prog_state -> outcome A.

Definition ret {A} (a : A) : M A := fun st => Ok a st.

Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
  fun st =>
    match m st with
    | Ok a st' => k a st'
    | Ub r => Ub r
    | Unmodelled w => Unmodelled w
    | Mismatch w => Mismatch w
    end.

Notation "x <- m ;; k" := (bind m (fun x => k))
  (at level 61, m at next level, right associativity).
Notation "m ;;; k" := (bind m (fun _ => k))
  (at level 61, right associativity).

Definition fail {A} (what : string) : M A := fun _ => Unmodelled what.
Definition raise {A} (r : ub_reason) : M A := fun _ => Ub r.
Definition get : M prog_state := fun st => Ok st st.
Definition put (st : prog_state) : M unit := fun _ => Ok tt st.

Definition of_access {A} (what : string) (r : access_result A) : M A :=
  fun st =>
    match r with
    | AccessOk a => Ok a st
    | AccessUb reason => Ub reason
    | AccessFail => Unmodelled what
    end.

Definition of_option {A} (what : string) (o : option A) : M A :=
  fun st => match o with Some a => Ok a st | None => Unmodelled what end.

Inductive result :=
  | Returned (v : runtime_value)
  | Panicked
  | Unwound.

Definition call_back : Type :=
  name -> list garg -> list runtime_value -> prog_state -> option (outcome result).

Definition oracle : Type :=
  call_back -> layout_env -> name -> list garg -> list runtime_value -> prog_state ->
  option (outcome result).

Definition callback_le (c1 c2 : call_back) : Prop :=
  forall f targs vs st o, c1 f targs vs st = Some o -> c2 f targs vs st = Some o.

Definition oracle_monotone (ext : oracle) : Prop :=
  forall c1 c2, callback_le c1 c2 ->
  forall env f targs vs st o,
    ext c1 env f targs vs st = Some o -> ext c2 env f targs vs st = Some o.

Definition model : Type :=
  layout_env -> name -> list garg -> list runtime_value -> M result.

Definition first_order (m : model) : oracle :=
  fun _ env f targs vs st => Some (m env f targs vs st).

Lemma first_order_monotone (m : model) : oracle_monotone (first_order m).
Proof. intros c1 c2 _ env f targs vs st o H. exact H. Qed.

Definition no_model : model := fun _ f _ _ => fail (String.append "no body for " f).

Definition no_models : oracle := first_order no_model.

Definition no_models_monotone : oracle_monotone no_models := first_order_monotone no_model.

Definition no_callback : call_back := fun _ _ _ _ => None.

Record program := MkProgram {
  pg_adts : list adt_def;
  pg_bodies : list body;
  pg_impls : list impl_def;
  pg_ext : oracle;
  pg_ext_monotone : oracle_monotone pg_ext;
}.

Definition only_adts (adts : list adt_def) : program :=
  MkProgram adts [] [] no_models no_models_monotone.

Definition is_phantom (t : ty) : bool :=
  match t with
  | TAdt p _ => String.eqb p "core::marker::PhantomData" || String.eqb p "std::marker::PhantomData"
  | _ => false
  end.

Definition transparent_tail (adts : list adt_def) (path : name) (args : list garg) : option ty :=
  match find (fun a => String.eqb (ad_path a) path) adts with
  | Some a =>
      if existsb (String.eqb "transparent") (ad_repr a) then
        match ad_kind a, ad_variants a with
        | AkStruct, [v] =>
            match rev (map (fun f => subst_ty args (snd f)) (vd_fields v)) with
            | TSlice e :: rest => if forallb is_phantom rest then Some (TSlice e) else None
            | TStr :: rest => if forallb is_phantom rest then Some TStr else None
            | _ => None
            end
        | _, _ => None
        end
      else None
  | None => None
  end.

Fixpoint normalize_ty_fuel (fuel : nat) (adts : list adt_def) (t : ty) : ty :=
  match fuel with
  | O => t
  | S fuel =>
      let go := normalize_ty_fuel fuel adts in
      let garg g := match g with GTy t' => GTy (go t') | _ => g end in
      match t with
      | TAdt p a =>
          match transparent_tail adts p a with
          | Some tail => go tail
          | None => TAdt p (map garg a)
          end
      | TArray e n => TArray (go e) n
      | TSlice e => TSlice (go e)
      | TRawPtr p m => TRawPtr (go p) m
      | TRef r p m => TRef r (go p) m
      | TTuple es => TTuple (map go es)
      | _ => t
      end
  end.

Definition normalize_ty (adts : list adt_def) (t : ty) : ty := normalize_ty_fuel 32 adts t.

Definition normalize_body (adts : list adt_def) (b : body) : body :=
  Body (bd_name b) (bd_file b) (bd_span b) (bd_generics b) (bd_bounds b) (bd_arg_count b)
    (map (fun d => LocalDecl (normalize_ty adts (ld_ty d)) (ld_mut d) (ld_name d) (ld_span d))
         (bd_locals b))
    (bd_blocks b) (bd_regions b) (bd_borrowck b).

Definition normalize_adts (adts : list adt_def) : list adt_def :=
  map (fun a =>
         AdtDef (ad_path a) (ad_kind a) (ad_generics a)
           (map (fun v => VariantDef (vd_name v) (vd_index v) (vd_discr v)
                            (map (fun f => (fst f, normalize_ty adts (snd f))) (vd_fields v)))
                (ad_variants a))
           (ad_repr a))
      adts.

Section Semantics.

Context `{Addr : AddrAlg}.

Definition layouts_of_body `{Alg : LayoutAlg} (adts : list adt_def) (b : body)
    : layout_env :=
  layout_env_of (normalize_adts adts) (map ld_ty (bd_locals b)).

Definition read (env : layout_env) (p : place) : M runtime_value :=
  fun st => of_access "read place" (read_place_result_with_layouts env p st) st.

Definition write (env : layout_env) (p : place) (v : runtime_value) : M unit :=
  fun st => match write_place_result_with_layouts env p v st with
            | AccessOk st' => Ok tt st'
            | AccessUb r => Ub r
            | AccessFail => Unmodelled "write place"
            end.

Definition bits_of (t : ty) : option (int_width * bool) :=
  match t with
  | TInt w => Some (w, true)
  | TUint w => Some (w, false)
  | _ => None
  end.

Definition width_bits (w : int_width) : Z :=
  match w with
  | W8 => 8%Z | W16 => 16%Z | W32 => 32%Z
  | W64 => 64%Z | W128 => 128%Z | WSize => 64%Z
  end.

Definition wrap (w : int_width) (signed : bool) (z : Z) : Z :=
  Z.modulo z (Z.pow 2%Z (width_bits w)).

Definition interp (w : int_width) (signed : bool) (z : Z) : Z :=
  if signed
  then let m := Z.pow 2%Z (width_bits w) in
       if Z.ltb z (Z.pow 2%Z (Z.sub (width_bits w) 1%Z)) then z else Z.sub z m
  else z.

Definition overflows (w : int_width) (signed : bool) (z : Z) : bool :=
  if signed
  then let h := Z.pow 2%Z (Z.sub (width_bits w) 1%Z) in
       orb (Z.ltb z (Z.opp h)) (Z.leb h z)
  else orb (Z.ltb z 0) (Z.leb (Z.pow 2%Z (width_bits w)) z).

Definition local_ty (b : body) (n : nat) : ty :=
  match nth_error (bd_locals b) n with
  | Some d => ld_ty d
  | None => TError "no such local"
  end.

Definition proj_ty (t : ty) (pe : proj_elem) : ty :=
  match pe with
  | PDeref =>
      match t with
      | TRef _ u _ | TRawPtr u _ => u
      | TAdt _ (GTy u :: _) => u
      | _ => TError "deref of a non-pointer type"
      end
  | PField _ u => u
  | PIndex _ | PConstantIndex _ _ _ =>
      match t with
      | TArray u _ | TSlice u => u
      | _ => TError "index into a non-array type"
      end
  | PSubslice _ _ _ => t
  | PDowncast _ _ => t
  | POpaqueCast u => u
  | PUnwrapUnsafeBinder u => u
  end.

Definition place_ty (b : body) (p : place) : ty :=
  fold_left proj_ty (pl_proj p) (local_ty b (pl_local p)).

Definition operand_ty (b : body) (o : operand) : ty :=
  match o with
  | OCopy p | OMove p => place_ty b p
  | OConst c =>
      match co_const c with
      | KTy t _ | KUnevaluated _ _ _ t | KVal _ t => t
      end
  | ORuntimeCheck _ => TBool
  end.

Definition const_value (t : ty) (v : const_value) : M runtime_value :=
  match v with
  | CvScalar (ScInt z _) =>
      match t with
      | TBool => ret (VBool (negb (Z.eqb z 0%Z)))
      | TChar => ret (VChar z)
      | TInt w => ret (VBits w (wrap w true z))
      | TUint w => ret (VBits w (wrap w false z))
      | _ => fail "scalar constant of a type outside the fragment"
      end
  | CvScalar (ScPtr _ _ _) => fail "pointer constant"
  | CvZeroSized => ret VUnit
  | CvSlice _ _ => fail "slice constant"
  | CvIndirect _ _ => fail "indirect constant"
  end.

Definition denote_const (P : program) (env : layout_env) (c : const_op) : M runtime_value :=
  match co_const c with
  | KVal v t => const_value t v
  | KTy t (CValue _ z) => const_value t (CvScalar (ScInt z 0))
  | KTy _ _ => fail "type-level constant that is not a value"
  | KUnevaluated path args None _ =>
      fun st =>
        match pg_ext P no_callback env path args [] st with
        | Some (Ok (Returned v) st') => Ok v st'
        | Some (Ok _ _) => Unmodelled "a constant that panics"
        | Some (Ub r) => Ub r
        | Some (Unmodelled w) => Unmodelled w
        | Some (Mismatch w) => Mismatch w
        | None => Unmodelled "a constant whose model does not finish"
        end
  | KUnevaluated _ _ (Some _) _ => fail "promoted constant"
  end.

Definition denote_operand (P : program) (env : layout_env) (o : operand) : M runtime_value :=
  match o with
  | OCopy p => read env p
  | OMove p =>
      v <- read env p ;;
      fun st => match deinitialize_place_with_layouts env p st with
                | Some st' => Ok v st'
                | None => Unmodelled "deinitialise at move"
                end
  | OConst c => denote_const P env c
  | ORuntimeCheck _ => fail "ORuntimeCheck"
  end.

Definition field_ty (t : ty) (i : nat) : ty :=
  match t with TTuple ts => nth i ts (TError "no such field") | _ => t end.

Definition bin_op_name (op : bin_op) : string :=
  match op with
  | BAdd => "BAdd" | BAddUnchecked => "BAddUnchecked" | BAddWithOverflow => "BAddWithOverflow"
  | BSub => "BSub" | BSubUnchecked => "BSubUnchecked" | BSubWithOverflow => "BSubWithOverflow"
  | BMul => "BMul" | BMulUnchecked => "BMulUnchecked" | BMulWithOverflow => "BMulWithOverflow"
  | BDiv => "BDiv" | BRem => "BRem"
  | BBitXor => "BBitXor" | BBitAnd => "BBitAnd" | BBitOr => "BBitOr"
  | BShl => "BShl" | BShlUnchecked => "BShlUnchecked"
  | BShr => "BShr" | BShrUnchecked => "BShrUnchecked"
  | BEq => "BEq" | BLt => "BLt" | BLe => "BLe" | BNe => "BNe" | BGe => "BGe" | BGt => "BGt"
  | BCmp => "BCmp" | BOffset => "BOffset"
  end.

Definition denote_binop (dst arg : ty) (op : bin_op) (a b : runtime_value)
    : M runtime_value :=
  match a, b with
  | VBits _ x, VBits _ y =>
      let arith k :=
        match bits_of dst with
        | Some (w, sg) =>
            ret (VBits w (wrap w sg (k (interp w sg x) (interp w sg y))))
        | None => fail "arithmetic into a non-integer destination"
        end in
      let checked k :=
        match bits_of (field_ty dst 0) with
        | Some (w, sg) =>
            let r := k (interp w sg x) (interp w sg y) in
            ret (VTuple [VBits w (wrap w sg r); VBool (overflows w sg r)])
        | None => fail "checked arithmetic into an unexpected destination"
        end in
      let divide k :=
        match bits_of dst with
        | Some (w, sg) =>
            let x' := interp w sg x in
            let y' := interp w sg y in
            if Z.eqb y' 0 then raise UbDivisionByZero
            else if sg && Z.eqb y' (-1) && Z.eqb x' (- 2 ^ (width_bits w - 1))
            then raise UbDivisionOverflow
            else ret (VBits w (wrap w sg (k x' y')))
        | None => fail "division into a non-integer destination"
        end in
      let compare k :=
        match bits_of arg with
        | Some (w, sg) => ret (VBool (k (interp w sg x) (interp w sg y)))
        | None => fail "comparison of operands that are not integers"
        end in
      match op with
      | BAdd => arith Z.add
      | BSub => arith Z.sub
      | BMul => arith Z.mul
      | BAddWithOverflow => checked Z.add
      | BSubWithOverflow => checked Z.sub
      | BMulWithOverflow => checked Z.mul
      | BDiv => divide Z.quot
      | BRem => divide Z.rem
      | BBitAnd => arith Z.land
      | BBitOr => arith Z.lor
      | BBitXor => arith Z.lxor
      | BEq => ret (VBool (Z.eqb x y))
      | BNe => ret (VBool (negb (Z.eqb x y)))
      | BLt => compare Z.ltb
      | BLe => compare Z.leb
      | BGt => compare (fun p q => Z.ltb q p)
      | BGe => compare (fun p q => Z.leb q p)
      | BAddUnchecked | BSubUnchecked | BMulUnchecked
      | BShl | BShlUnchecked | BShr | BShrUnchecked
      | BCmp | BOffset => fail (bin_op_name op)
      end
  | VBool p, VBool q =>
      match op with
      | BEq => ret (VBool (Bool.eqb p q))
      | BNe => ret (VBool (negb (Bool.eqb p q)))
      | BBitAnd => ret (VBool (andb p q))
      | BBitOr => ret (VBool (orb p q))
      | BBitXor => ret (VBool (xorb p q))
      | BLt => ret (VBool (andb (negb p) q))
      | BLe => ret (VBool (orb (negb p) q))
      | BGt => ret (VBool (andb p (negb q)))
      | BGe => ret (VBool (orb p (negb q)))
      | BAdd | BAddUnchecked | BAddWithOverflow
      | BSub | BSubUnchecked | BSubWithOverflow
      | BMul | BMulUnchecked | BMulWithOverflow
      | BDiv | BRem | BShl | BShlUnchecked | BShr | BShrUnchecked
      | BCmp | BOffset => fail (String.append "boolean " (bin_op_name op))
      end
  | _, _ => fail "operands outside the fragment"
  end.

Definition denote_unop (dst : ty) (op : un_op) (v : runtime_value)
    : M runtime_value :=
  match op with
  | UNot =>
      match v with
      | VBool b => ret (VBool (negb b))
      | VBits _ z =>
          match bits_of dst with
          | Some (w, s) => ret (VBits w (wrap w s (Z.lnot z)))
          | None => fail "complement into a non-integer destination"
          end
      | _ => fail "complement of a value outside the fragment"
      end
  | UNeg =>
      match v with
      | VBits _ z =>
          match bits_of dst with
          | Some (w, s) => ret (VBits w (wrap w s (Z.opp z)))
          | None => fail "negation into a non-integer destination"
          end
      | _ => fail "negation of a value outside the fragment"
      end
  | UPtrMetadata => fail "UPtrMetadata"
  end.

Fixpoint denote_operands (P : program) (env : layout_env) (os : list operand)
    : M (list runtime_value) :=
  match os with
  | [] => ret []
  | o :: rest =>
      v <- denote_operand P env o ;;
      vs <- denote_operands P env rest ;;
      ret (v :: vs)
  end.

Definition discriminant_of (adts : list adt_def) (path : name) (k : variant) : option Z :=
  match find (fun a => String.eqb (ad_path a) path) adts with
  | Some a =>
      match find (fun v => Nat.eqb (vd_index v) k) (ad_variants a) with
      | Some v => Some (vd_discr v)
      | None => None
      end
  | None => None
  end.

Definition denote_cast (src dst : ty) (v : runtime_value) : M runtime_value :=
  match bits_of dst with
  | Some (w', sg') =>
      match v with
      | VBits w z =>
          match bits_of src with
          | Some (_, sg) => ret (VBits w' (wrap w' sg' (interp w sg z)))
          | None => fail "integer cast from a type that is not an integer"
          end
      | VBool b => ret (VBits w' (if b then 1%Z else 0%Z))
      | VChar z => ret (VBits w' (wrap w' sg' z))
      | _ => fail "integer cast of a value that is not an integer"
      end
  | None => fail "integer cast to a type that is not an integer"
  end.

Definition denote_rvalue (P : program) (env : layout_env) (b : body) (dst : ty)
    (r : rvalue) : M runtime_value :=
  match r with
  | RUse o _ => denote_operand P env o
  | RBinaryOp op x y =>
      vx <- denote_operand P env x ;;
      vy <- denote_operand P env y ;;
      denote_binop dst (operand_ty b x) op vx vy
  | RUnaryOp op o => v <- denote_operand P env o ;; denote_unop dst op v
  | RCast CkIntToInt o t => v <- denote_operand P env o ;; denote_cast (operand_ty b o) t v
  | RRef _ _ p | RRawPtr _ p =>
      fun st => match address_of_place_with_layouts env p st with
                | Some v => Ok v st
                | None => Unmodelled "address of place"
                end
  | RAggregate AgTuple fs =>
      vs <- denote_operands P env fs ;; ret (VTuple vs)
  | RAggregate (AgAdt path v _ None) fs =>
      vs <- denote_operands P env fs ;; ret (VAdt path v vs)
  | RAggregate (AgAdt _ _ _ (Some _)) _ => fail "union aggregate"
  | RDiscriminant p =>
      v <- read env p ;;
      match v with
      | VAdt path k _ =>
          d <- of_option "discriminant of an ADT with no definition"
                 (discriminant_of (pg_adts P) path k) ;;
          match bits_of dst with
          | Some (w, sg) => ret (VBits w (wrap w sg d))
          | None => fail "discriminant into a non-integer destination"
          end
      | _ => fail "discriminant of a non-enum value"
      end
  | RAggregate (AgArray _) _ => fail "AgArray"
  | RAggregate (AgClosure _ _) _ => fail "AgClosure"
  | RAggregate (AgCoroutine _ _) _ => fail "AgCoroutine"
  | RAggregate (AgCoroutineClosure _ _) _ => fail "AgCoroutineClosure"
  | RAggregate (AgRawPtr _ _) _ => fail "AgRawPtr"
  | RRepeat _ _ => fail "RRepeat"
  | RThreadLocalRef _ => fail "RThreadLocalRef"
  | RCast _ _ _ => fail "RCast other than an integer cast"
  | RCopyForDeref _ => fail "RCopyForDeref"
  | RWrapUnsafeBinder _ _ => fail "RWrapUnsafeBinder"
  | RReborrow _ _ _ => fail "RReborrow"
  end.

Fixpoint has_storage_live (l : local) (ss : list statement) : bool :=
  match ss with
  | [] => false
  | s :: rest =>
      match st_kind s with
      | SStorageLive l' => Nat.eqb l l' || has_storage_live l rest
      | _ => has_storage_live l rest
      end
  end.

Definition always_live (b : body) (l : local) : bool :=
  negb (existsb (fun blk => has_storage_live l (bb_stmts blk)) (bd_blocks b)).

Definition allocate_at_entry (env : layout_env) (b : body) (l : local)
    (st : prog_state) : option prog_state :=
  match shape_of_layout_ty (local_ty b l) with
  | Some (ShapeAdtType t) =>
      match find_type_layout env t with
      | Some _ => storage_live_local_with_layouts env (ShapeAdtType t) l st
      | None => Some st
      end
  | Some sh => storage_live_local_with_layouts env sh l st
  | None => Some st
  end.

Definition free_frame (env : layout_env) (b : body) : M unit :=
  fun st =>
    let step acc l :=
      match acc with
      | Some s =>
          match nth_error (state_locals s) l with
          | Some (LocalAllocated _) => storage_dead_local_with_layouts env l s
          | _ => Some s
          end
      | None => None
      end in
    match fold_left step (seq 0 (length (bd_locals b))) (Some st) with
    | Some st' => Ok tt st'
    | None => Unmodelled "free the frame at return"
    end.

Definition denote_statement (P : program) (env : layout_env) (b : body)
    (s : statement) : M unit :=
  match st_kind s with
  | SAssign p r =>
      v <- denote_rvalue P env b (place_ty b p) r ;;
      write env p v
  | SStorageLive l =>
      sh <- of_option "shape of local" (shape_of_layout_ty (local_ty b l)) ;;
      fun st => match storage_live_local_with_layouts env sh l st with
                | Some st' => Ok tt st'
                | None => Unmodelled "storage live"
                end
  | SStorageDead l =>
      fun st => match storage_dead_local_with_layouts env l st with
                | Some st' => Ok tt st'
                | None => Unmodelled "storage dead"
                end
  | SSetDiscriminant p v =>
      cur <- read env p ;;
      match cur with
      | VAdt d _ fs => write env p (VAdt d v fs)
      | _ => fail "set discriminant on a non-enum value"
      end
  | SFakeRead _ _ | SAscribeUserType _ _ _ | SPlaceMention _
  | SNop | SConstEvalCounter | SCoverage _
  | SBackwardIncompatibleDropHint _ _ => ret tt
  | SIntrinsic _ => fail "SIntrinsic"
  end.

Fixpoint denote_statements (P : program) (env : layout_env) (b : body)
    (ss : list statement) : M unit :=
  match ss with
  | [] => ret tt
  | s :: rest => denote_statement P env b s ;;; denote_statements P env b rest
  end.



Definition substitution : Type := list (nat * garg).

Definition bind_param (i : nat) (g : garg) (sub : substitution) : option substitution :=
  match find (fun p => Nat.eqb (fst p) i) sub with
  | Some (_, g') => if garg_eqb g g' then Some sub else None
  | None => Some ((i, g) :: sub)
  end.

Definition match_tconst (p c : tconst) (sub : substitution) : option substitution :=
  match p with
  | CParam i _ => bind_param i (GConst c) sub
  | _ => if tconst_eqb p c then Some sub else None
  end.

Fixpoint match_ty (p t : ty) (sub : substitution) {struct p} : option substitution :=
  let fix gargs (ps ts : list garg) (sub : substitution) : option substitution :=
    match ps, ts with
    | [], [] => Some sub
    | p :: ps, t :: ts =>
        match match_garg p t sub with
        | Some sub => gargs ps ts sub
        | None => None
        end
    | _, _ => None
    end in
  let fix tys (ps ts : list ty) (sub : substitution) : option substitution :=
    match ps, ts with
    | [], [] => Some sub
    | p :: ps, t :: ts =>
        match match_ty p t sub with
        | Some sub => tys ps ts sub
        | None => None
        end
    | _, _ => None
    end in
  match p, t with
  | TParam i _, _ => bind_param i (GTy t) sub
  | TAdt x ps, TAdt y ts => if String.eqb x y then gargs ps ts sub else None
  | TRef _ p' m, TRef _ t' m' | TRawPtr p' m, TRawPtr t' m' =>
      if mutability_eqb m m' then match_ty p' t' sub else None
  | TSlice p', TSlice t' => match_ty p' t' sub
  | TArray p' n, TArray t' k =>
      match match_ty p' t' sub with
      | Some sub => match_tconst n k sub
      | None => None
      end
  | TTuple ps, TTuple ts => tys ps ts sub
  | _, _ => if ty_eqb p t then Some sub else None
  end

with match_garg (p g : garg) (sub : substitution) {struct p} : option substitution :=
  match p, g with
  | GTy x, GTy y => match_ty x y sub
  | GConst x, GConst y => match_tconst x y sub
  | GLifetime _, GLifetime _ => Some sub
  | _, _ => None
  end.

Fixpoint match_gargs (ps ts : list garg) (sub : substitution) : option substitution :=
  match ps, ts with
  | [], [] => Some sub
  | p :: ps, t :: ts =>
      match match_garg p t sub with
      | Some sub => match_gargs ps ts sub
      | None => None
      end
  | _, _ => None
  end.

Definition param_index (g : generic_param) : nat :=
  match g with GpTy i _ | GpLifetime i _ | GpConst i _ _ => i end.

Fixpoint impl_params (gs : list generic_param) (sub : substitution) : option (list garg) :=
  match gs with
  | [] => Some []
  | g :: gs =>
      let this :=
        match find (fun p => Nat.eqb (fst p) (param_index g)) sub, g with
        | Some (_, a), _ => Some a
        | None, GpLifetime _ _ => Some (GLifetime RErased)
        | None, _ => None
        end in
      match this, impl_params gs sub with
      | Some a, Some rest => Some (a :: rest)
      | _, _ => None
      end
  end.

Definition impl_target (f : name) (targs : list garg) (i : impl_def)
    : option (name * list garg) :=
  if ip_negative i then None else
  match find (fun it => String.eqb (fst it) f) (ip_items i) with
  | None => None
  | Some (_, item) =>
      let n := length (ip_args i) in
      match match_gargs (ip_args i) (firstn n targs) [] with
      | None => None
      | Some sub =>
          match impl_params (ip_generics i) sub with
          | Some own => Some (item, (own ++ skipn n targs)%list)
          | None => None
          end
      end
  end.

Fixpoint first_some {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: rest => match f x with Some y => Some y | None => first_some f rest end
  end.

Definition find_body (P : program) (f : name) : option body :=
  find (fun b => String.eqb (bd_name b) f) (pg_bodies P).

Inductive callee :=
  | CalleeBody (b : body)
  | CalleeModel (f : name) (targs : list garg).

Definition resolve (P : program) (f : name) (targs : list garg) : callee :=
  let '(g, gargs) :=
    match first_some (impl_target f targs) (pg_impls P) with
    | Some target => target
    | None => (f, targs)
    end in
  match find_body P g with
  | Some b => CalleeBody (normalize_body (pg_adts P) (subst_body gargs b))
  | None => CalleeModel g gargs
  end.

Definition callee_of (b : body) (o : operand) : option (name * list garg) :=
  match o with
  | OConst c =>
      match co_const c with
      | KVal _ (TFnDef f targs) => Some (f, targs)
      | _ => None
      end
  | OCopy (Place l []) | OMove (Place l []) =>
      match local_ty b l with
      | TFnDef f targs => Some (f, targs)
      | _ => None
      end
  | _ => None
  end.

Fixpoint args_match (b : body) (i : nat) (args : list runtime_value) : bool :=
  match args with
  | [] => true
  | v :: rest =>
      match nth_error (bd_locals b) (S i) with
      | Some d => shape_matches_ty (shape_of_value v) (ld_ty d) && args_match b (S i) rest
      | None => false
      end
  end.

Definition check_args (b : body) (args : list runtime_value) : option string :=
  if negb (Nat.eqb (length args) (bd_arg_count b))
  then Some "wrong number of arguments"
  else if negb (args_match b 0 args)
  then Some "argument does not match the declared type"
  else None.

Definition enter_frame (env : layout_env) (b : body) (args : list runtime_value)
    (st : prog_state) : option prog_state :=
  let n := length (bd_locals b) in
  let base := state_with_locals st (repeat LocalUnallocated n) in
  let rest := seq (S (bd_arg_count b)) (n - S (bd_arg_count b)) in
  let live := 0 :: seq 1 (bd_arg_count b) ++ filter (always_live b) rest in
  let allocated :=
    fold_left (fun acc l => match acc with
                            | Some st => allocate_at_entry env b l st
                            | None => None
                            end)
              live (Some base) in
  fold_left (fun acc (iv : nat * runtime_value) =>
               match acc with
               | Some st => write_place_with_layouts env (Place (S (fst iv)) []) (snd iv) st
               | None => None
               end)
            (combine (seq 0 (length args)) args) allocated.

Definition entry_state_from (env : layout_env) (b : body) (memory : memory_state)
    (args : list runtime_value) : option prog_state :=
  enter_frame env b args (ByteState [] memory).

Definition entry_state (env : layout_env) (b : body) (args : list runtime_value)
    : option prog_state :=
  entry_state_from env b [] args.

Definition merge_layouts (env extra : layout_env) : layout_env :=
  (env ++ filter (fun l => negb (existsb (fun l' => ty_eqb (layout_ty l') (layout_ty l)) env))
                 extra)%list.

Inductive control :=
  | Goto (n : block_id)
  | Finish (r : result)
  | Enter (callee : body) (env : layout_env) (saved : list local_storage)
          (dest : place) (target : option block_id)
  | Model (f : name) (targs : list garg) (args : list runtime_value)
          (dest : place) (target : option block_id).

Fixpoint switch_target (z : Z) (ts : list (Z * block_id)) (otherwise : block_id)
    : block_id :=
  match ts with
  | [] => otherwise
  | (v, t) :: rest => if Z.eqb v z then t else switch_target z rest otherwise
  end.

Definition scalar_of (v : runtime_value) : option Z :=
  match v with
  | VBits _ z => Some z
  | VBool b => Some (if b then 1%Z else 0%Z)
  | VChar z => Some z
  | _ => None
  end.

Definition return_to (env : layout_env) (dest : place) (target : option block_id)
    (v : runtime_value) : M block_id :=
  match target with
  | Some t => write env dest v ;;; ret t
  | None => raise UbReachedUnreachable
  end.

Definition denote_call `{Alg : LayoutAlg} (P : program) (env : layout_env) (b : body)
    (func : operand) (args : list operand) (dest : place) (target : option block_id)
    : M control :=
  match callee_of b func with
  | None => fail "callee is not a function item"
  | Some (f, targs) =>
      vs <- denote_operands P env args ;;
      fun st =>
        match resolve P f targs with
        | CalleeBody callee =>
            match check_args callee vs with
            | Some why => Mismatch why
            | None =>
                let env' := merge_layouts env (layouts_of_body (pg_adts P) callee) in
                match enter_frame env' callee vs st with
                | Some st' => Ok (Enter callee env' (state_locals st) dest target) st'
                | None => Unmodelled "allocate the frame at entry"
                end
            end
        | CalleeModel g gargs => Ok (Model g gargs vs dest target) st
        end
  end.

Definition denote_terminator `{Alg : LayoutAlg} (P : program) (env : layout_env) (b : body)
    (t : terminator) : M control :=
  match tm_kind t with
  | TGoto n => ret (Goto n)
  | TReturn =>
      v <- read env (Place 0 []) ;;
      free_frame env b ;;;
      ret (Finish (Returned v))
  | TSwitchInt d ts o =>
      v <- denote_operand P env d ;;
      match scalar_of v with
      | Some z => ret (Goto (switch_target z ts o))
      | None => fail "switchInt on a non-scalar"
      end
  | TAssert c expected _ target _ =>
      v <- denote_operand P env c ;;
      match v with
      | VBool bb => if Bool.eqb bb expected then ret (Goto target)
                    else ret (Finish Panicked)
      | _ => fail "assert on a non-boolean"
      end
  | TDrop p target _ _ _ =>
      fun st =>
        match place_initialized_result env p st with
        | AccessOk true =>
            match deinitialize_place_with_layouts env p st with
            | Some st' => Ok (Goto target) st'
            | None => Unmodelled "deinitialise at drop"
            end
        | AccessOk false | AccessUb UbReadUninitialized => Ok (Goto target) st
        | AccessUb r => Ub r
        | AccessFail => Unmodelled "place at drop"
        end
  | TCall func args dest target _ _ _ => denote_call P env b func args dest target
  | TFalseEdge real _ => ret (Goto real)
  | TFalseUnwind real _ => ret (Goto real)
  | TUnreachable => raise UbReachedUnreachable
  | TUnwindResume => ret (Finish Unwound)
  | TUnwindTerminate _ => fail "TUnwindTerminate"
  | TTailCall _ _ _ => fail "TTailCall"
  | TYield _ _ _ _ => fail "TYield"
  | TCoroutineDrop => fail "TCoroutineDrop"
  | TInlineAsm _ _ _ _ _ _ => fail "TInlineAsm"
  end.

Definition find_block (b : body) (n : block_id) : option basic_block :=
  find (fun blk => Nat.eqb (bb_id blk) n) (bd_blocks b).

Definition denote_block `{Alg : LayoutAlg} (P : program) (env : layout_env) (b : body)
    (n : block_id) : M control :=
  match find_block b n with
  | None => fail "no such block"
  | Some blk =>
      denote_statements P env b (bb_stmts blk) ;;;
      denote_terminator P env b (bb_term blk)
  end.

Definition callback_with `{Alg : LayoutAlg} (P : program)
    (run : layout_env -> body -> prog_state -> option (outcome result))
    (env : layout_env) : call_back :=
  fun f targs args st0 =>
    match resolve P f targs with
    | CalleeBody callee =>
        match check_args callee args with
        | Some why => Some (Mismatch why)
        | None =>
            let env' := merge_layouts env (layouts_of_body (pg_adts P) callee) in
            match enter_frame env' callee args st0 with
            | Some st1 =>
                match run env' callee st1 with
                | Some (Ok r st2) => Some (Ok r (state_with_locals st2 (state_locals st0)))
                | o => o
                end
            | None => Some (Unmodelled "allocate the frame at entry")
            end
        end
    | CalleeModel _ _ => Some (Unmodelled "a model calling a function without a body")
    end.

Lemma callback_with_le `{Alg : LayoutAlg} (P : program) run1 run2 env :
  (forall env' callee st o, run1 env' callee st = Some o -> run2 env' callee st = Some o) ->
  callback_le (callback_with P run1 env) (callback_with P run2 env).
Proof.
  intros H f targs args st0 o E. unfold callback_with in *.
  destruct (resolve P f targs) as [callee|]; [|exact E].
  destruct (check_args callee args); [exact E|].
  destruct (enter_frame _ callee args st0) as [st1|]; [|exact E].
  destruct (run1 _ callee st1) as [o1|] eqn:E1; [|discriminate].
  rewrite (H _ _ _ _ E1). exact E.
Qed.

Fixpoint run_block `{Alg : LayoutAlg} (P : program) (n : nat) (env : layout_env) (b : body)
    (l : block_id) (st : prog_state) : option (outcome result) :=
  match n with
  | O => None
  | S n' =>
      match denote_block P env b l st with
      | Ok (Goto l') st' => run_block P n' env b l' st'
      | Ok (Finish r) st' => Some (Ok r st')
      | Ok (Enter callee env' saved dest target) st' =>
          match run_block P n' env' callee 0 st' with
          | Some (Ok (Returned v) st'') =>
              match return_to env dest target v (state_with_locals st'' saved) with
              | Ok t st3 => run_block P n' env b t st3
              | Ub r => Some (Ub r)
              | Unmodelled w => Some (Unmodelled w)
              | Mismatch w => Some (Mismatch w)
              end
          | Some (Ok r st'') => Some (Ok r (state_with_locals st'' saved))
          | Some (Ub r) => Some (Ub r)
          | Some (Unmodelled w) => Some (Unmodelled w)
          | Some (Mismatch w) => Some (Mismatch w)
          | None => None
          end
      | Ok (Model g gargs vs dest target) st' =>
          match pg_ext P (callback_with P (fun env' callee st1 => run_block P n' env' callee 0 st1)
                           env) env g gargs vs st' with
          | Some (Ok (Returned v) st'') =>
              match return_to env dest target v (state_with_locals st'' (state_locals st')) with
              | Ok t st3 => run_block P n' env b t st3
              | Ub r => Some (Ub r)
              | Unmodelled w => Some (Unmodelled w)
              | Mismatch w => Some (Mismatch w)
              end
          | Some (Ok r st'') => Some (Ok r (state_with_locals st'' (state_locals st')))
          | Some (Ub r) => Some (Ub r)
          | Some (Unmodelled w) => Some (Unmodelled w)
          | Some (Mismatch w) => Some (Mismatch w)
          | None => None
          end
      | Ub r => Some (Ub r)
      | Unmodelled w => Some (Unmodelled w)
      | Mismatch w => Some (Mismatch w)
      end
  end.

Lemma run_block_call `{Alg : LayoutAlg} (P : program) n env b l st callee env' saved dest
    target st' :
  denote_block P env b l st = Ok (Enter callee env' saved dest target) st' ->
  run_block P (S n) env b l st =
    match run_block P n env' callee 0 st' with
    | Some (Ok (Returned v) st'') =>
        match return_to env dest target v (state_with_locals st'' saved) with
        | Ok t st3 => run_block P n env b t st3
        | Ub r => Some (Ub r)
        | Unmodelled w => Some (Unmodelled w)
        | Mismatch w => Some (Mismatch w)
        end
    | Some (Ok r st'') => Some (Ok r (state_with_locals st'' saved))
    | Some (Ub r) => Some (Ub r)
    | Some (Unmodelled w) => Some (Unmodelled w)
    | Some (Mismatch w) => Some (Mismatch w)
    | None => None
    end.
Proof. intros H. cbn [run_block]. rewrite H. reflexivity. Qed.

Lemma run_block_monotone `{Alg : LayoutAlg} (P : program) :
  forall n m env b l st o,
    n <= m -> run_block P n env b l st = Some o -> run_block P m env b l st = Some o.
Proof.
  induction n as [|n IH]; intros m env b l st o Hle H; [discriminate|].
  destruct m as [|m]; [lia|].
  cbn [run_block] in *.
  destruct (denote_block P env b l st) as [k st'| | |]; try exact H.
  destruct k as [l'|r|callee env' saved dest target|g gargs vs dest target].
  - apply IH; [lia | exact H].
  - exact H.
  - destruct (run_block P n env' callee 0 st') as [o1|] eqn:E1; [|discriminate].
    rewrite (IH m env' callee 0 st' o1 ltac:(lia) E1).
    destruct o1 as [[v| |] st''| | |]; try exact H.
    destruct (return_to env dest target v (state_with_locals st'' saved)) as [t st3| | |];
      try exact H.
    apply IH; [lia | exact H].
  - destruct (pg_ext P _ env g gargs vs st') as [o1|] eqn:E1; [|discriminate].
    rewrite (pg_ext_monotone P _ _
               (callback_with_le P _ _ env
                  (fun env' callee st1 o2 H2 => IH m env' callee 0 st1 o2 ltac:(lia) H2))
               env g gargs vs st' o1 E1).
    destruct o1 as [[v| |] st''| | |]; try exact H.
    destruct (return_to env dest target v _) as [t st3| | |]; try exact H.
    apply IH; [lia | exact H].
Qed.

Definition entry_body (P : program) (b : body) : body := normalize_body (pg_adts P) b.

Definition run_with `{Alg : LayoutAlg} (P : program) (b : body) (memory : memory_state)
    (args : list runtime_value) : bounded (outcome result) :=
  fun n =>
    let b := entry_body P b in
    match check_args b args with
    | Some why => Some (Mismatch why)
    | None =>
        let env := layouts_of_body (pg_adts P) b in
        match entry_state_from env b memory args with
        | Some st => run_block P n env b 0 st
        | None => Some (Unmodelled "allocate the frame at entry")
        end
    end.

Lemma run_with_monotone `{Alg : LayoutAlg} (P : program) b memory args :
  Monotone (run_with P b memory args).
Proof.
  intros n m o Hle H. unfold run_with in *.
  destruct (check_args (entry_body P b) args); [exact H|].
  destruct (entry_state_from _ (entry_body P b) memory args); [|exact H].
  exact (run_block_monotone P n m _ _ 0 _ o Hle H).
Qed.

Definition run_from `{Alg : LayoutAlg} (adts : list adt_def) (b : body)
    (memory : memory_state) (args : list runtime_value) : bounded (outcome result) :=
  run_with (only_adts adts) b memory args.

Definition run_in `{Alg : LayoutAlg} (adts : list adt_def) (b : body) (args : list runtime_value)
    : bounded (outcome result) :=
  run_from adts b [] args.

Definition run `{Alg : LayoutAlg} (b : body) (args : list runtime_value)
    : bounded (outcome result) :=
  run_in [] b args.

Definition run_at `{Alg : LayoutAlg} (b : body) (targs : list garg)
    (args : list runtime_value) : bounded (outcome result) :=
  run (subst_body targs b) args.

Definition peek {A} (n : nat) (d : bounded A) : option A := d n.

Lemma peek_terminates {A} : forall n (d : bounded A) a,
  peek n d = Some a -> Terminates d a.
Proof. intros n d a H. exists n. exact H. Qed.

Theorem terminates_deterministic {A} : forall (d : bounded A) a a',
  Monotone d -> Terminates d a -> Terminates d a' -> a = a'.
Proof.
  intros d a a' Hm [n Hn] [n' Hn'].
  destruct (Nat.le_ge_cases n n') as [Hle|Hle].
  - rewrite (Hm n n' a Hle Hn) in Hn'. congruence.
  - rewrite (Hm n' n a' Hle Hn') in Hn. congruence.
Qed.

Theorem not_both {A} : forall (d : bounded A) a, Terminates d a -> ~ Diverges d.
Proof. intros d a [n Hn] Hd. rewrite (Hd n) in Hn. discriminate. Qed.

Fixpoint advance `{Alg : LayoutAlg} (P : program) (env : layout_env) (b : body) (k : nat)
    (l : block_id) (st : prog_state) : option (block_id * prog_state) :=
  match k with
  | O => Some (l, st)
  | S k' =>
      match denote_block P env b l st with
      | Ok (Goto l') st' => advance P env b k' l' st'
      | _ => None
      end
  end.

Lemma advance_add `{Alg : LayoutAlg} (P : program) env b : forall i j l st,
  advance P env b (i + j) l st =
  match advance P env b i l st with
  | Some (l', st') => advance P env b j l' st'
  | None => None
  end.
Proof.
  induction i as [|i IH]; intros j l st; [reflexivity|].
  cbn. destruct (denote_block P env b l st) as [[l'| | |] st'| | |]; try reflexivity.
  apply IH.
Qed.

Lemma diverges_after `{Alg : LayoutAlg} (P : program) env b : forall j l st l' st',
  advance P env b j l st = Some (l', st') ->
  (forall n, run_block P n env b l' st' = None) ->
  forall n, run_block P n env b l st = None.
Proof.
  induction j as [|j IH]; intros l st l' st' H Hd n; cbn in H.
  - injection H as <- <-. apply Hd.
  - destruct (denote_block P env b l st) as [[l1| | |] st1| | |] eqn:E; try discriminate.
    destruct n as [|n]; [reflexivity|].
    cbn [run_block]. rewrite E. exact (IH l1 st1 l' st' H Hd n).
Qed.

Lemma diverges_by_invariant `{Alg : LayoutAlg} (P : program) env b
    (Inv : block_id -> prog_state -> Prop) :
  (forall l st, Inv l st ->
     exists l' st', denote_block P env b l st = Ok (Goto l') st' /\ Inv l' st') ->
  forall l st, Inv l st -> forall n, run_block P n env b l st = None.
Proof.
  intros Hstep l st Hinv n. revert l st Hinv.
  induction n as [|n IH]; intros l st Hinv; [reflexivity|].
  destruct (Hstep l st Hinv) as [l' [st' [E Hinv']]].
  cbn [run_block]. rewrite E. exact (IH l' st' Hinv').
Qed.

Lemma diverges_by_cycle `{Alg : LayoutAlg} (P : program) env b (j k : nat) l st :
  match advance P env b j l st with
  | Some (l0, st0) => advance P env b (S k) l0 st0 = Some (l0, st0)
  | None => False
  end ->
  forall n, run_block P n env b l st = None.
Proof.
  destruct (advance P env b j l st) as [[l0 st0]|] eqn:Hj; [|contradiction].
  intros Hcycle. apply (diverges_after P env b j l st l0 st0 Hj).
  assert (Hinv : forall n i l' st', i <= k -> advance P env b i l0 st0 = Some (l', st') ->
            run_block P n env b l' st' = None).
  { induction n as [|n IH]; intros i l' st' Hi Hadv; [reflexivity|].
    assert (Hsplit : S k = i + S (k - i)) by lia.
    pose proof Hcycle as Hc. rewrite Hsplit, advance_add, Hadv in Hc. cbn in Hc.
    destruct (denote_block P env b l' st') as [[l''| | |] st''| | |] eqn:E; try discriminate.
    cbn [run_block]. rewrite E.
    destruct (Nat.eq_dec i k) as [->|Hne].
    - rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as -> ->.
      apply (IH 0); [lia | reflexivity].
    - apply (IH (S i)); [lia|].
      replace (S i) with (i + 1) by apply Nat.add_1_r.
      rewrite advance_add, Hadv. cbn. rewrite E. reflexivity. }
  intros n. apply (Hinv n 0); [lia | reflexivity].
Qed.

Lemma diverges_in_callee `{Alg : LayoutAlg} (P : program) env b l st :
  match denote_block P env b l st with
  | Ok (Enter callee env' _ _ _) st' => forall n, run_block P n env' callee 0 st' = None
  | _ => False
  end ->
  forall n, run_block P n env b l st = None.
Proof.
  destruct (denote_block P env b l st) as [[| |callee env' saved dest target|] st'| | |] eqn:E;
    try contradiction.
  intros Hd n. destruct n as [|n]; [reflexivity|].
  rewrite (run_block_call P n env b l st callee env' saved dest target st' E), Hd.
  reflexivity.
Qed.

Lemma diverges_in_cycling_callee `{Alg : LayoutAlg} (P : program) env b l st (j k : nat) :
  match denote_block P env b l st with
  | Ok (Enter callee env' _ _ _) st' =>
      match advance P env' callee j 0 st' with
      | Some (l0, st0) => advance P env' callee (S k) l0 st0 = Some (l0, st0)
      | None => False
      end
  | _ => False
  end ->
  forall n, run_block P n env b l st = None.
Proof.
  intros H. apply diverges_in_callee.
  destruct (denote_block P env b l st) as [[| |callee env' saved dest target|] st'| | |];
    try contradiction.
  exact (diverges_by_cycle P env' callee j k 0 st' H).
Qed.

Lemma run_with_diverges `{Alg : LayoutAlg} (P : program) b memory args :
  match check_args (entry_body P b) args with
  | Some _ => False
  | None =>
      match entry_state_from (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b)
              memory args with
      | Some st =>
          forall n, run_block P n (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b)
                      0 st = None
      | None => False
      end
  end ->
  Diverges (run_with P b memory args).
Proof.
  intros H n. unfold run_with.
  destruct (check_args (entry_body P b) args); [contradiction|].
  destruct (entry_state_from _ (entry_body P b) memory args); [|contradiction].
  apply H.
Qed.

Lemma run_with_cycles `{Alg : LayoutAlg} (P : program) b memory args (j k : nat) :
  match check_args (entry_body P b) args,
        entry_state_from (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b)
          memory args with
  | None, Some st =>
      match advance P (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b) j 0 st with
      | Some (l0, st0) =>
          advance P (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b) (S k) l0 st0
            = Some (l0, st0)
      | None => False
      end
  | _, _ => False
  end ->
  Diverges (run_with P b memory args).
Proof.
  intros H. apply run_with_diverges.
  destruct (check_args (entry_body P b) args); [contradiction|].
  destruct (entry_state_from _ (entry_body P b) memory args); [|contradiction].
  exact (diverges_by_cycle P _ _ j k 0 _ H).
Qed.

Lemma run_with_calls_cycling `{Alg : LayoutAlg} (P : program) b memory args (j k : nat) :
  match check_args (entry_body P b) args,
        entry_state_from (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b)
          memory args with
  | None, Some st =>
      match denote_block P (layouts_of_body (pg_adts P) (entry_body P b)) (entry_body P b) 0 st with
      | Ok (Enter callee env' _ _ _) st' =>
          match advance P env' callee j 0 st' with
          | Some (l0, st0) => advance P env' callee (S k) l0 st0 = Some (l0, st0)
          | None => False
          end
      | _ => False
      end
  | _, _ => False
  end ->
  Diverges (run_with P b memory args).
Proof.
  intros H. apply run_with_diverges.
  destruct (check_args (entry_body P b) args); [contradiction|].
  destruct (entry_state_from _ (entry_body P b) memory args); [|contradiction].
  exact (diverges_in_cycling_callee P _ _ 0 _ j k H).
Qed.

Inductive answer :=
  | ARet (v : runtime_value)
  | APanic
  | AUnwind
  | AUb (reason : ub_reason)
  | AUnmodelled (what : string)
  | AMismatch (what : string).

Definition answer_of (o : outcome result) : answer :=
  match o with
  | Ok (Returned v) _ => ARet v
  | Ok Panicked _ => APanic
  | Ok Unwound _ => AUnwind
  | Ub r => AUb r
  | Unmodelled w => AUnmodelled w
  | Mismatch w => AMismatch w
  end.

Definition MeansUnder `{Alg : LayoutAlg} (P : program) (b : body) (args : list runtime_value)
    (a : answer) : Prop :=
  exists o, Terminates (run_with P b [] args) o /\ answer_of o = a.

Definition MeansOn `{Alg : LayoutAlg} (P : program) (b : body) (memory : memory_state)
    (args : list runtime_value) (a : answer) : Prop :=
  exists o, Terminates (run_with P b memory args) o /\ answer_of o = a.

Lemma means_on_within `{Alg : LayoutAlg} (P : program) (n : nat) :
  forall b memory args a,
    option_map answer_of (peek n (run_with P b memory args)) = Some a ->
    MeansOn P b memory args a.
Proof.
  intros b memory args a H.
  destruct (peek n (run_with P b memory args)) as [o|] eqn:E; cbn in H; [|discriminate].
  exists o. split; [ apply (peek_terminates n); exact E | congruence ].
Qed.

Definition MeansIn `{Alg : LayoutAlg} (adts : list adt_def) (b : body) (args : list runtime_value)
    (a : answer) : Prop :=
  MeansUnder (only_adts adts) b args a.

Definition Means `{Alg : LayoutAlg} (b : body) (args : list runtime_value) (a : answer) : Prop :=
  MeansIn [] b args a.

Definition MeansAt `{Alg : LayoutAlg} (b : body) (targs : list garg)
    (args : list runtime_value) (a : answer) : Prop :=
  Means (subst_body targs b) args a.

Theorem means_under_deterministic `{Alg : LayoutAlg} (P : program) :
  forall b args a a', MeansUnder P b args a -> MeansUnder P b args a' -> a = a'.
Proof.
  intros b args a a' [o [Ht Ha]] [o' [Ht' Ha']].
  rewrite (terminates_deterministic _ _ _ (run_with_monotone P b [] args) Ht Ht') in Ha.
  congruence.
Qed.

Theorem means_in_deterministic `{Alg : LayoutAlg} :
  forall adts b args a a', MeansIn adts b args a -> MeansIn adts b args a' -> a = a'.
Proof. intros adts. apply means_under_deterministic. Qed.

Theorem means_deterministic `{Alg : LayoutAlg} :
  forall b args a a', Means b args a -> Means b args a' -> a = a'.
Proof. intros; eapply means_in_deterministic; eauto. Qed.

Lemma means_under_within `{Alg : LayoutAlg} (P : program) (n : nat) :
  forall b args a,
    option_map answer_of (peek n (run_with P b [] args)) = Some a ->
    MeansUnder P b args a.
Proof.
  intros b args a H.
  destruct (peek n (run_with P b [] args)) as [o|] eqn:E; cbn in H; [|discriminate].
  exists o. split; [ apply (peek_terminates n); exact E | congruence ].
Qed.

Lemma means_within_in `{Alg : LayoutAlg} (adts : list adt_def) (n : nat) :
  forall b args a,
    option_map answer_of (peek n (run_in adts b args)) = Some a ->
    MeansIn adts b args a.
Proof. intros b args a H. exact (means_under_within (only_adts adts) n b args a H). Qed.

Lemma means_within `{Alg : LayoutAlg} (n : nat) :
  forall b args a,
    option_map answer_of (peek n (run b args)) = Some a ->
    Means b args a.
Proof. intros. apply (means_within_in [] n). exact H. Qed.

Definition final_state (o : outcome result) : option prog_state :=
  match o with
  | Ok _ st => Some st
  | _ => None
  end.

Definition MeansWith `{Alg : LayoutAlg} (P : program) (b : body)
    (memory : memory_state) (args : list runtime_value)
    (a : answer) (st : option prog_state) : Prop :=
  exists o, Terminates (run_with P b memory args) o
    /\ answer_of o = a /\ final_state o = st.

Definition MeansFrom `{Alg : LayoutAlg} (adts : list adt_def) (b : body)
    (memory : memory_state) (args : list runtime_value)
    (a : answer) (st : option prog_state) : Prop :=
  MeansWith (only_adts adts) b memory args a st.

Theorem means_with_deterministic `{Alg : LayoutAlg} (P : program) :
  forall b memory args a a' st st',
    MeansWith P b memory args a st -> MeansWith P b memory args a' st' ->
    a = a' /\ st = st'.
Proof.
  intros b memory args a a' st st' [o [Ht [Ha Hs]]] [o' [Ht' [Ha' Hs']]].
  rewrite (terminates_deterministic _ _ _ (run_with_monotone P b memory args) Ht Ht')
    in Ha, Hs.
  split; congruence.
Qed.

Theorem means_from_deterministic `{Alg : LayoutAlg} :
  forall adts b memory args a a' st st',
    MeansFrom adts b memory args a st -> MeansFrom adts b memory args a' st' ->
    a = a' /\ st = st'.
Proof. intros adts. apply means_with_deterministic. Qed.

Lemma means_with_within `{Alg : LayoutAlg} (P : program) (n : nat) :
  forall b memory args a st,
    option_map (fun o => (answer_of o, final_state o)) (peek n (run_with P b memory args))
      = Some (a, st) ->
    MeansWith P b memory args a st.
Proof.
  intros b memory args a st H.
  destruct (peek n (run_with P b memory args)) as [o|] eqn:E; cbn in H; [|discriminate].
  injection H as Ha Hs.
  exists o. split; [ apply (peek_terminates n); exact E | split; assumption ].
Qed.

Lemma means_from_within `{Alg : LayoutAlg} (adts : list adt_def) (n : nat) :
  forall b memory args a st,
    option_map (fun o => (answer_of o, final_state o)) (peek n (run_from adts b memory args))
      = Some (a, st) ->
    MeansFrom adts b memory args a st.
Proof.
  intros b memory args a st H. exact (means_with_within (only_adts adts) n b memory args a st H).
Qed.

End Semantics.

#[global] Existing Instance bump_addr.

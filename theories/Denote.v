From RustRocq Require Import Syntax Subst LayoutAlg Memory.
From Stdlib Require Import Bool String List ZArith Lia.
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
Definition mismatch {A} (why : string) : M A := fun _ => Mismatch why.
Definition current_locals : M (list local_storage) := fun st => Ok (state_locals st) st.

Definition of_access {A} (what : string) (r : access_result A) : M A :=
  fun st =>
    match r with
    | AccessOk a => Ok a st
    | AccessUb reason => Ub reason
    | AccessFail => Unmodelled what
    end.

Definition of_option {A} (what : string) (o : option A) : M A :=
  fun st => match o with Some a => Ok a st | None => Unmodelled what end.

Definition observe {A} (what : string) (f : prog_state -> access_result A) : M A :=
  fun st => of_access what (f st) st.

Definition change (what : string) (f : prog_state -> access_result prog_state) : M unit :=
  fun st =>
    match f st with
    | AccessOk st' => Ok tt st'
    | AccessUb r => Ub r
    | AccessFail => Unmodelled what
    end.

Inductive result :=
  | Returned (v : runtime_value)
  | Panicked
  | Unwound.

Section Programs.

  Definition call_back : Type :=
    name -> list garg -> list runtime_value -> prog_state -> option (outcome result).

  Definition oracle : Type :=
    call_back -> list adt_def -> name -> list garg -> list runtime_value -> prog_state ->
    option (outcome result).

  Definition callback_le (c1 c2 : call_back) : Prop :=
    forall f targs vs st o, c1 f targs vs st = Some o -> c2 f targs vs st = Some o.

  Definition oracle_monotone (ext : oracle) : Prop :=
    forall c1 c2, callback_le c1 c2 ->
    forall adts f targs vs st o,
      ext c1 adts f targs vs st = Some o -> ext c2 adts f targs vs st = Some o.

  Definition model : Type :=
    list adt_def -> name -> list garg -> list runtime_value -> M result.

  Definition first_order (m : model) : oracle :=
    fun _ adts f targs vs st => Some (m adts f targs vs st).

  Lemma first_order_monotone (m : model) : oracle_monotone (first_order m).
  Proof. intros c1 c2 _ adts f targs vs st o H. exact H. Qed.

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

  Definition frame_tys (b : body) : list ty := map ld_ty (bd_locals b).

End Programs.

Section Operators.

  Definition bits_of (t : ty) : option (int_width * bool) :=
    match t with
    | TInt w => Some (w, true)
    | TUint w => Some (w, false)
    | _ => None
    end.

  Definition width_bits (w : int_width) : Z := Z.of_nat (8 * int_width_bytes w).

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

  Definition is_trait_object_pointer (t : ty) : bool :=
    match t with
    | TRef _ (TDynamic _ _) _ | TRawPtr (TDynamic _ _) _ => true
    | _ => false
    end.

  Definition denote_unsize (src dst : ty) (v : runtime_value) : M runtime_value :=
    match v, src with
    | VPtr (PointerValue provenance address PointerThin), (TRef _ pointee _ | TRawPtr pointee _) =>
        if is_trait_object_pointer dst
        then ret (VPtr (PointerValue provenance address (PointerVTable pointee)))
        else fail "unsizing cast other than to a trait object"
    | VPtr (PointerValue _ _ (PointerVTable _)), _ =>
        if is_trait_object_pointer dst
        then ret v
        else fail "unsizing cast of a trait object to something other than a trait object"
    | _, _ => fail "unsizing cast of a value that is neither a thin pointer nor a trait object"
    end.

End Operators.

Section Typing.

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
        | _ => TError "deref of a non-pointer type"
        end
    | PField _ u => u
    | PIndex _ | PConstantIndex _ _ _ =>
        match t with
        | TArray u _ | TSlice u => u
        | _ => TError "index into a non-array type"
        end
    | PSubslice _ _ _ | PDowncast _ _ => t
    | POpaqueCast u | PUnwrapUnsafeBinder u => u
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

  Definition discriminant_of (adts : list adt_def) (path : name) (k : variant) : option Z :=
    match find_adt adts path with
    | Some a =>
        match find (fun v => Nat.eqb (vd_index v) k) (ad_variants a) with
        | Some v => Some (vd_discr v)
        | None => None
        end
    | None => None
    end.

End Typing.

Section Expressions.

  Context `{Alg : LayoutAlg} (P : program) (b : body).

  Definition read (p : place) : M runtime_value :=
    observe "read place" (fun st => read_place (pg_adts P) (frame_tys b) st p).

  Definition write (p : place) (v : runtime_value) : M unit :=
    change "write place" (fun st => write_place (pg_adts P) (frame_tys b) st p v).

  Definition deinit (p : place) : M unit :=
    change "deinitialise place" (fun st => deinit_place (pg_adts P) (frame_tys b) st p).

  Definition address_of (p : place) : M runtime_value :=
    observe "address of place" (fun st => address_of_place (pg_adts P) (frame_tys b) st p).

  Definition static_data (t : ty) : M nat :=
    fun st =>
      match allocate_uninit (pg_adts P) (state_memory st) t with
      | Some (id, memory) => Ok id (state_with_memory st memory)
      | None => Unmodelled "allocate the data of a constant"
      end.

  Definition static_pointer (t : ty) (offset : Z) (meta : pointer_metadata) : M runtime_value :=
    id <- static_data t ;;
    ret (VPtr (PointerValue (ProvenanceAllocation id) offset meta)).

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
    | CvScalar (ScPtr _ offset _) =>
        match t with
        | TRef _ pointee _ | TRawPtr pointee _ => static_pointer pointee offset PointerThin
        | _ => fail "pointer constant of a type that is not a pointer"
        end
    | CvZeroSized => ret VUnit
    | CvSlice _ n =>
        let array_of e := TArray e (CValue (TUint WSize) n) in
        match t with
        | TRef _ TStr _ => static_pointer (array_of (TUint W8)) 0 (PointerLength (Z.to_nat n))
        | TRef _ (TSlice e) _ => static_pointer (array_of e) 0 (PointerLength (Z.to_nat n))
        | _ => fail "slice constant of a type that is not a slice reference"
        end
    | CvIndirect _ _ => fail "indirect constant"
    end.

  Definition denote_const (c : const_op) : M runtime_value :=
    match co_const c with
    | KVal v t => const_value t v
    | KTy t (CValue _ z) => const_value t (CvScalar (ScInt z 0))
    | KTy _ _ => fail "type-level constant that is not a value"
    | KUnevaluated path args None _ =>
        fun st =>
          match pg_ext P no_callback (pg_adts P) path args [] st with
          | Some (Ok (Returned v) st') => Ok v st'
          | Some (Ok _ _) => Unmodelled "a constant that panics"
          | Some (Ub r) => Ub r
          | Some (Unmodelled w) => Unmodelled w
          | Some (Mismatch w) => Mismatch w
          | None => Unmodelled "a constant whose model does not finish"
          end
    | KUnevaluated _ _ (Some _) _ => fail "promoted constant"
    end.

  Definition denote_operand (o : operand) : M runtime_value :=
    match o with
    | OCopy p => read p
    | OMove p => v <- read p ;; deinit p ;;; ret v
    | OConst c => denote_const c
    | ORuntimeCheck _ => fail "ORuntimeCheck"
    end.

  Fixpoint denote_operands (os : list operand) : M (list runtime_value) :=
    match os with
    | [] => ret []
    | o :: rest =>
        v <- denote_operand o ;;
        vs <- denote_operands rest ;;
        ret (v :: vs)
    end.

  Definition denote_rvalue (dst : ty) (r : rvalue) : M runtime_value :=
    match r with
    | RUse o _ => denote_operand o
    | RBinaryOp op x y =>
        vx <- denote_operand x ;;
        vy <- denote_operand y ;;
        denote_binop dst (operand_ty b x) op vx vy
    | RUnaryOp op o => v <- denote_operand o ;; denote_unop dst op v
    | RCast CkIntToInt o t => v <- denote_operand o ;; denote_cast (operand_ty b o) t v
    | RCast (CkPointerCoercion PcUnsize _) o t =>
        v <- denote_operand o ;; denote_unsize (operand_ty b o) t v
    | RRef _ _ p | RRawPtr _ p => address_of p
    | RAggregate AgTuple fs => vs <- denote_operands fs ;; ret (VTuple vs)
    | RAggregate (AgAdt path v _ None) fs => vs <- denote_operands fs ;; ret (VAdt path v vs)
    | RAggregate (AgAdt _ _ _ (Some _)) _ => fail "union aggregate"
    | RAggregate (AgArray _) fs => vs <- denote_operands fs ;; ret (VArray vs)
    | RAggregate (AgClosure _ _) fs => vs <- denote_operands fs ;; ret (VTuple vs)
    | RDiscriminant p =>
        v <- read p ;;
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

  Definition denote_statement (s : statement) : M unit :=
    match st_kind s with
    | SAssign p r => v <- denote_rvalue (place_ty b p) r ;; write p v
    | SStorageLive x =>
        change "storage live" (fun st => required (storage_live (pg_adts P) (frame_tys b) st x))
    | SStorageDead x => change "storage dead" (fun st => required (storage_dead st x))
    | SFakeRead _ _ | SAscribeUserType _ _ _ | SPlaceMention _
    | SNop | SConstEvalCounter | SCoverage _
    | SBackwardIncompatibleDropHint _ _ => ret tt
    | SSetDiscriminant _ _ => fail "SSetDiscriminant"
    | SIntrinsic _ => fail "SIntrinsic"
    end.

  Fixpoint denote_statements (ss : list statement) : M unit :=
    match ss with
    | [] => ret tt
    | s :: rest => denote_statement s ;;; denote_statements rest
    end.

  Definition initialized (p : place) : M bool :=
    fun st =>
      match place_initialized (pg_adts P) (frame_tys b) st p with
      | AccessUb UbReadUninitialized => Ok false st
      | r => of_access "place at drop" r st
      end.

  Definition free_frame : M unit :=
    change "free the frame at return" (fun st =>
      required (fold_left (fun acc x => match acc with
                                        | Some st => storage_dead st x
                                        | None => None
                                        end)
                          (seq 0 (length (bd_locals b))) (Some st))).

End Expressions.

Section Resolution.

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
    | Some b => CalleeBody (subst_body gargs b)
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

End Resolution.

Section Frames.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition check_args (callee : body) (args : list runtime_value) : option string :=
    if negb (Nat.eqb (length args) (bd_arg_count callee))
    then Some "wrong number of arguments"
    else if negb (forallb (fun '(t, v) => encodable adts t v)
                          (combine (tl (frame_tys callee)) args))
    then Some "argument does not match the declared type"
    else None.

  Fixpoint has_storage_live (x : local) (ss : list statement) : bool :=
    match ss with
    | [] => false
    | s :: rest =>
        match st_kind s with
        | SStorageLive x' => Nat.eqb x x' || has_storage_live x rest
        | _ => has_storage_live x rest
        end
    end.

  Definition always_live (callee : body) (x : local) : bool :=
    negb (existsb (fun blk => has_storage_live x (bb_stmts blk)) (bd_blocks callee)).

  Definition enter_frame (callee : body) (args : list runtime_value) (st : prog_state)
      : access_result prog_state :=
    let tys := frame_tys callee in
    let n := length tys in
    let others := seq (S (bd_arg_count callee)) (n - S (bd_arg_count callee)) in
    let live := 0 :: seq 1 (bd_arg_count callee) ++ filter (always_live callee) others in
    let fresh := state_with_locals st (repeat LocalUnallocated n) in
    let allocated :=
      fold_left (fun st x => match storage_live adts tys st x with
                             | Some st' => st'
                             | None => st
                             end)
                live fresh in
    fold_left (fun acc '(i, v) => st <-? acc ;; write_place adts tys st (Place (S i) []) v)
              (combine (seq 0 (length args)) args) (AccessOk allocated).

  Definition start_call (callee : body) (args : list runtime_value) : M unit :=
    match check_args callee args with
    | Some why => mismatch why
    | None =>
        change (String.append "allocate the frame at entry of " (bd_name callee))
          (enter_frame callee args)
    end.

End Frames.

Section Running.

  Context `{Alg : LayoutAlg}.

  Inductive control :=
    | Goto (n : block_id)
    | Finish (r : result)
    | Enter (callee : body) (saved : list local_storage) (dest : place) (target : option block_id)
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

  Definition denote_call (P : program) (b : body) (func : operand) (args : list operand)
      (dest : place) (target : option block_id) : M control :=
    match callee_of b func with
    | None => fail "callee is not a function item"
    | Some (f, targs) =>
        vs <- denote_operands P b args ;;
        match resolve P f targs with
        | CalleeBody callee =>
            saved <- current_locals ;;
            start_call (pg_adts P) callee vs ;;;
            ret (Enter callee saved dest target)
        | CalleeModel g gargs => ret (Model g gargs vs dest target)
        end
    end.

  Definition denote_terminator (P : program) (b : body) (t : terminator) : M control :=
    match tm_kind t with
    | TGoto n => ret (Goto n)
    | TReturn =>
        v <- read P b (Place 0 []) ;;
        free_frame b ;;;
        ret (Finish (Returned v))
    | TSwitchInt d ts o =>
        v <- denote_operand P b d ;;
        match scalar_of v with
        | Some z => ret (Goto (switch_target z ts o))
        | None => fail "switchInt on a non-scalar"
        end
    | TAssert c expected _ target _ =>
        v <- denote_operand P b c ;;
        match v with
        | VBool bb => if Bool.eqb bb expected then ret (Goto target) else ret (Finish Panicked)
        | _ => fail "assert on a non-boolean"
        end
    | TDrop p target _ _ _ =>
        live <- initialized P b p ;;
        (if live then deinit P b p else ret tt) ;;;
        ret (Goto target)
    | TCall func args dest target _ _ _ => denote_call P b func args dest target
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

  Definition denote_block (P : program) (b : body) (n : block_id) : M control :=
    match find_block b n with
    | None => fail "no such block"
    | Some blk => denote_statements P b (bb_stmts blk) ;;; denote_terminator P b (bb_term blk)
    end.

  Definition callback_with (P : program) (run : body -> prog_state -> option (outcome result))
      : call_back :=
    fun f targs args st0 =>
      match resolve P f targs with
      | CalleeBody callee =>
          match start_call (pg_adts P) callee args st0 with
          | Ok _ st1 =>
              match run callee st1 with
              | Some (Ok r st2) => Some (Ok r (state_with_locals st2 (state_locals st0)))
              | o => o
              end
          | Ub r => Some (Ub r)
          | Unmodelled w => Some (Unmodelled w)
          | Mismatch w => Some (Mismatch w)
          end
      | CalleeModel _ _ => Some (Unmodelled "a model calling a function without a body")
      end.

  Lemma callback_with_le (P : program) run1 run2 :
    (forall callee st o, run1 callee st = Some o -> run2 callee st = Some o) ->
    callback_le (callback_with P run1) (callback_with P run2).
  Proof.
    intros H f targs args st0 o E. unfold callback_with in *.
    destruct (resolve P f targs) as [callee|]; [|exact E].
    destruct (start_call _ callee args st0) as [_ st1| | |]; try exact E.
    destruct (run1 callee st1) as [o1|] eqn:E1; [|discriminate].
    rewrite (H _ _ _ E1). exact E.
  Qed.

  Definition return_to (P : program) (b : body) (dest : place) (target : option block_id)
      (v : runtime_value) : M block_id :=
    match target with
    | Some t => write P b dest v ;;; ret t
    | None => raise UbReachedUnreachable
    end.

  Definition after_call (P : program) (b : body) (dest : place) (target : option block_id)
      (saved : list local_storage) (continue : block_id -> prog_state -> option (outcome result))
      (called : option (outcome result)) : option (outcome result) :=
    match called with
    | Some (Ok (Returned v) st) =>
        match return_to P b dest target v (state_with_locals st saved) with
        | Ok t st' => continue t st'
        | Ub r => Some (Ub r)
        | Unmodelled w => Some (Unmodelled w)
        | Mismatch w => Some (Mismatch w)
        end
    | Some (Ok r st) => Some (Ok r (state_with_locals st saved))
    | Some (Ub r) => Some (Ub r)
    | Some (Unmodelled w) => Some (Unmodelled w)
    | Some (Mismatch w) => Some (Mismatch w)
    | None => None
    end.

  Fixpoint run_block (P : program) (n : nat) (b : body) (l : block_id) (st : prog_state)
      : option (outcome result) :=
    match n with
    | O => None
    | S n' =>
        match denote_block P b l st with
        | Ok (Goto l') st' => run_block P n' b l' st'
        | Ok (Finish r) st' => Some (Ok r st')
        | Ok (Enter callee saved dest target) st' =>
            after_call P b dest target saved (run_block P n' b) (run_block P n' callee 0 st')
        | Ok (Model g gargs vs dest target) st' =>
            after_call P b dest target (state_locals st') (run_block P n' b)
              (pg_ext P (callback_with P (fun callee => run_block P n' callee 0))
                      (pg_adts P) g gargs vs st')
        | Ub r => Some (Ub r)
        | Unmodelled w => Some (Unmodelled w)
        | Mismatch w => Some (Mismatch w)
        end
    end.

  Lemma after_call_le (P : program) b dest target saved c1 c2 called o :
    (forall t st o, c1 t st = Some o -> c2 t st = Some o) ->
    after_call P b dest target saved c1 called = Some o ->
    after_call P b dest target saved c2 called = Some o.
  Proof.
    intros Hc H. unfold after_call in *.
    destruct called as [[[v| |] st| | |]|]; try exact H.
    destruct (return_to P b dest target v _) as [t st'| | |]; try exact H.
    apply Hc. exact H.
  Qed.

  Lemma run_block_monotone (P : program) :
    forall n m b l st o,
      n <= m -> run_block P n b l st = Some o -> run_block P m b l st = Some o.
  Proof.
    induction n as [|n IH]; intros m b l st o Hle H; [discriminate|].
    destruct m as [|m]; [lia|].
    assert (Hrun : forall b' l' st' o', run_block P n b' l' st' = Some o' ->
                                        run_block P m b' l' st' = Some o')
      by (intros; apply IH; [lia | assumption]).
    cbn [run_block] in *.
    destruct (denote_block P b l st) as [k st'| | |]; try exact H.
    destruct k as [l'|r|callee saved dest target|g gargs vs dest target].
    - apply Hrun. exact H.
    - exact H.
    - destruct (run_block P n callee 0 st') as [o1|] eqn:E; [|discriminate].
      rewrite (Hrun _ _ _ _ E).
      exact (after_call_le P b dest target saved _ _ _ _ (Hrun b) H).
    - destruct (pg_ext P _ _ g gargs vs st') as [o1|] eqn:E; [|discriminate].
      rewrite (pg_ext_monotone P _ _
                 (callback_with_le P (fun callee => run_block P n callee 0)
                    (fun callee => run_block P m callee 0) (fun callee => Hrun callee 0))
                 _ g gargs vs st' o1 E).
      exact (after_call_le P b dest target _ _ _ _ _ (Hrun b) H).
  Qed.

  Lemma run_block_call (P : program) n b l st callee saved dest target st' :
    denote_block P b l st = Ok (Enter callee saved dest target) st' ->
    run_block P (S n) b l st =
      after_call P b dest target saved (run_block P n b) (run_block P n callee 0 st').
  Proof. intros H. cbn [run_block]. rewrite H. reflexivity. Qed.

  Definition run_with (P : program) (b : body) (memory : memory_state)
      (args : list runtime_value) : bounded (outcome result) :=
    fun n =>
      match start_call (pg_adts P) b args (ByteState [] memory) with
      | Ok _ st => run_block P n b 0 st
      | Ub r => Some (Ub r)
      | Unmodelled w => Some (Unmodelled w)
      | Mismatch w => Some (Mismatch w)
      end.

  Lemma run_with_monotone (P : program) b memory args : Monotone (run_with P b memory args).
  Proof.
    intros n m o Hle H. unfold run_with in *.
    destruct (start_call _ b args _) as [_ st| | |]; try exact H.
    exact (run_block_monotone P n m b 0 st o Hle H).
  Qed.

  Theorem terminates_deterministic {A} : forall (d : bounded A) a a',
    Monotone d -> Terminates d a -> Terminates d a' -> a = a'.
  Proof.
    intros d a a' Hm [n Hn] [n' Hn'].
    destruct (Nat.le_ge_cases n n') as [Hle|Hle].
    - rewrite (Hm n n' a Hle Hn) in Hn'. congruence.
    - rewrite (Hm n' n a' Hle Hn') in Hn. congruence.
  Qed.

End Running.

Section Divergence.

  Context `{Alg : LayoutAlg} (P : program).

  Fixpoint advance (b : body) (k : nat) (l : block_id) (st : prog_state)
      : option (block_id * prog_state) :=
    match k with
    | O => Some (l, st)
    | S k' =>
        match denote_block P b l st with
        | Ok (Goto l') st' => advance b k' l' st'
        | _ => None
        end
    end.

  Lemma advance_add b : forall i j l st,
    advance b (i + j) l st =
    match advance b i l st with
    | Some (l', st') => advance b j l' st'
    | None => None
    end.
  Proof.
    induction i as [|i IH]; intros j l st; [reflexivity|].
    cbn. destruct (denote_block P b l st) as [[l'| | |] st'| | |]; try reflexivity.
    apply IH.
  Qed.

  Lemma diverges_after b : forall j l st l' st',
    advance b j l st = Some (l', st') ->
    (forall n, run_block P n b l' st' = None) ->
    forall n, run_block P n b l st = None.
  Proof.
    induction j as [|j IH]; intros l st l' st' H Hd n; cbn in H.
    - injection H as <- <-. apply Hd.
    - destruct (denote_block P b l st) as [[l1| | |] st1| | |] eqn:E; try discriminate.
      destruct n as [|n]; [reflexivity|].
      cbn [run_block]. rewrite E. exact (IH l1 st1 l' st' H Hd n).
  Qed.

  Lemma diverges_by_cycle b (j k : nat) l st :
    match advance b j l st with
    | Some (l0, st0) => advance b (S k) l0 st0 = Some (l0, st0)
    | None => False
    end ->
    forall n, run_block P n b l st = None.
  Proof.
    destruct (advance b j l st) as [[l0 st0]|] eqn:Hj; [|contradiction].
    intros Hcycle. apply (diverges_after b j l st l0 st0 Hj).
    assert (Hinv : forall n i l' st', i <= k -> advance b i l0 st0 = Some (l', st') ->
              run_block P n b l' st' = None).
    { induction n as [|n IH]; intros i l' st' Hi Hadv; [reflexivity|].
      assert (Hsplit : S k = i + S (k - i)) by lia.
      pose proof Hcycle as Hc. rewrite Hsplit, advance_add, Hadv in Hc. cbn in Hc.
      destruct (denote_block P b l' st') as [[l''| | |] st''| | |] eqn:E; try discriminate.
      cbn [run_block]. rewrite E.
      destruct (Nat.eq_dec i k) as [->|Hne].
      - rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as -> ->.
        apply (IH 0); [lia | reflexivity].
      - apply (IH (S i)); [lia|].
        replace (S i) with (i + 1) by apply Nat.add_1_r.
        rewrite advance_add, Hadv. cbn. rewrite E. reflexivity. }
    intros n. apply (Hinv n 0); [lia | reflexivity].
  Qed.

  Lemma diverges_in_cycling_callee b l st (j k : nat) :
    match denote_block P b l st with
    | Ok (Enter callee _ _ _) st' =>
        match advance callee j 0 st' with
        | Some (l0, st0) => advance callee (S k) l0 st0 = Some (l0, st0)
        | None => False
        end
    | _ => False
    end ->
    forall n, run_block P n b l st = None.
  Proof.
    destruct (denote_block P b l st) as [[| |callee saved dest target|] st'| | |] eqn:E;
      try contradiction.
    intros Hcycle n. destruct n as [|n]; [reflexivity|].
    rewrite (run_block_call P n b l st callee saved dest target st' E).
    rewrite (diverges_by_cycle callee j k 0 st' Hcycle n). reflexivity.
  Qed.

  Lemma run_with_calls_cycling b memory args (j k : nat) :
    match start_call (pg_adts P) b args (ByteState [] memory) with
    | Ok _ st =>
        match denote_block P b 0 st with
        | Ok (Enter callee _ _ _) st' =>
            match advance callee j 0 st' with
            | Some (l0, st0) => advance callee (S k) l0 st0 = Some (l0, st0)
            | None => False
            end
        | _ => False
        end
    | _ => False
    end ->
    Diverges (run_with P b memory args).
  Proof.
    intros H n. unfold run_with.
    destruct (start_call _ b args _) as [_ st| | |]; try contradiction.
    exact (diverges_in_cycling_callee b 0 st j k H n).
  Qed.

End Divergence.

Section Meaning.

  Context `{Alg : LayoutAlg}.

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

  Definition final_state (o : outcome result) : option prog_state :=
    match o with
    | Ok _ st => Some st
    | _ => None
    end.

  Definition Means (P : program) (b : body) (memory : memory_state) (args : list runtime_value)
      (a : answer) : Prop :=
    exists o, Terminates (run_with P b memory args) o /\ answer_of o = a.

  Definition MeansWith (P : program) (b : body) (memory : memory_state)
      (args : list runtime_value) (a : answer) (st : option prog_state) : Prop :=
    exists o, Terminates (run_with P b memory args) o /\ answer_of o = a /\ final_state o = st.

  Lemma means_within (P : program) (n : nat) b memory args a :
    option_map answer_of (run_with P b memory args n) = Some a -> Means P b memory args a.
  Proof.
    intros H. destruct (run_with P b memory args n) as [o|] eqn:E; cbn in H; [|discriminate].
    exists o. split; [exists n; exact E | congruence].
  Qed.

  Lemma means_with_within (P : program) (n : nat) b memory args a st :
    option_map (fun o => (answer_of o, final_state o)) (run_with P b memory args n)
      = Some (a, st) ->
    MeansWith P b memory args a st.
  Proof.
    intros H. destruct (run_with P b memory args n) as [o|] eqn:E; cbn in H; [|discriminate].
    injection H as Ha Hs. exists o. split; [exists n; exact E | split; assumption].
  Qed.

  Theorem means_deterministic (P : program) b memory args a a' :
    Means P b memory args a -> Means P b memory args a' -> a = a'.
  Proof.
    intros [o [Ht Ha]] [o' [Ht' Ha']].
    rewrite (terminates_deterministic _ _ _ (run_with_monotone P b memory args) Ht Ht') in Ha.
    congruence.
  Qed.

End Meaning.

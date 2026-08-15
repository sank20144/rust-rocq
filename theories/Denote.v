From RustRocq Require Import Syntax Layout Memory Subst.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Inductive outcome (A : Type) :=
  | Ok (a : A) (st : prog_state)
  | Ub (reason : ub_reason)
  | Unmodelled (what : string)
  | Mismatch (what : string)
  | OutOfFuel.

Arguments Ok {A} _ _.
Arguments Ub {A} _.
Arguments Unmodelled {A} _.
Arguments Mismatch {A} _.
Arguments OutOfFuel {A}.

Definition M (A : Type) : Type := prog_state -> outcome A.

Definition ret {A} (a : A) : M A := fun st => Ok a st.

Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
  fun st =>
    match m st with
    | Ok a st' => k a st'
    | Ub r => Ub r
    | Unmodelled w => Unmodelled w
    | Mismatch w => Mismatch w
    | OutOfFuel => OutOfFuel
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

Fixpoint iter {A B} (fuel : nat) (step : A -> M (A + B)) (a : A) : M B :=
  match fuel with
  | 0 => fun _ => OutOfFuel
  | S f =>
      r <- step a ;;
      match r with
      | inl a' => iter f step a'
      | inr b => ret b
      end
  end.

Fixpoint packed_offsets (at_ : nat) (ts : list ty) : list nat :=
  match ts with
  | [] => []
  | t :: rest =>
      let sz := match shape_of_layout_ty t with
                | Some sh => shape_size_with_layouts [] sh
                | None => 0%nat
                end in
      at_ :: packed_offsets (at_ + sz) rest
  end.

Definition packed_layout (t : ty) (sh : value_shape) : type_layout :=
  let fields := match t with
                | TTuple ts => ts
                | TAdt _ _ => []
                | _ => []
                end in
  let fl := match t with
            | TTuple ts => FieldsArbitrary (packed_offsets 0%nat ts)
            | TArray e n =>
                FieldsArray (match shape_of_layout_ty e with
                             | Some esh => shape_size_with_layouts [] esh
                             | None => 0%nat
                             end)
                            (match const_nat n with Some k => k | None => 0%nat end)
            | _ => FieldsPrimitive
            end in
  TypeLayoutData "packed" t
    (shape_size_with_layouts [] sh) (shape_align_with_layouts [] sh)
    false fields fl (VariantsSingle 0%nat) (AbiMemory true).

Fixpoint shapes_of (fuel : nat) (t : ty) : list (ty * value_shape) :=
  match fuel with
  | 0%nat => []
  | S f =>
      let here := match shape_of_layout_ty t with
                  | Some sh => [(t, sh)]
                  | None => []
                  end in
      let inner := match t with
                   | TTuple ts => concat (map (shapes_of f) ts)
                   | TArray e _ | TSlice e => shapes_of f e
                   | TRef _ p _ | TRawPtr p _ => shapes_of f p
                   | _ => []
                   end in
      here ++ inner
  end.

Fixpoint dedup (acc : list ty) (xs : list (ty * value_shape)) : list type_layout :=
  match xs with
  | [] => []
  | (t, sh) :: rest =>
      if existsb (ty_eqb t) acc
      then dedup acc rest
      else packed_layout t sh :: dedup (t :: acc) rest
  end.

Definition layouts_of_body (b : body) : layout_env :=
  dedup [] (concat (map (fun d => shapes_of 32%nat (ld_ty d)) (bd_locals b))).

Definition read (env : layout_env) (p : place) : M runtime_value :=
  fun st => of_access "read place" (read_place_result_with_layouts env p st) st.

Definition write (env : layout_env) (p : place) (v : runtime_value) : M unit :=
  fun st => match write_place_with_layouts env p v st with
            | Some st' => Ok tt st'
            | None => Unmodelled "write place"
            end.

Definition const_value (t : ty) (v : const_value) : M runtime_value :=
  match v, t with
  | CvScalar (ScInt z _), TBool => ret (VBool (negb (Z.eqb z 0%Z)))
  | CvScalar (ScInt z _), TChar => ret (VChar z)
  | CvScalar (ScInt z _), TInt w => ret (VBits w z)
  | CvScalar (ScInt z _), TUint w => ret (VBits w z)
  | CvZeroSized, _ => ret VUnit
  | _, _ => fail "constant outside the fragment"
  end.

Definition denote_const (c : const_op) : M runtime_value :=
  match co_const c with
  | KVal v t => const_value t v
  | _ => fail "unevaluated constant"
  end.

Definition denote_operand (env : layout_env) (o : operand) : M runtime_value :=
  match o with
  | OCopy p | OMove p => read env p
  | OConst c => denote_const c
  | ORuntimeCheck _ => ret (VBool true)
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

Definition field_ty (t : ty) (i : nat) : ty :=
  match t with TTuple ts => nth i ts (TError "no such field") | _ => t end.

Definition denote_binop (dst : ty) (op : bin_op) (a b : runtime_value)
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
      match op with
      | BAdd => arith Z.add
      | BSub => arith Z.sub
      | BMul => arith Z.mul
      | BAddWithOverflow => checked Z.add
      | BSubWithOverflow => checked Z.sub
      | BMulWithOverflow => checked Z.mul
      | BDiv => if Z.eqb y 0%Z then raise UbInvalidScalar else arith Z.quot
      | BRem => if Z.eqb y 0%Z then raise UbInvalidScalar else arith Z.rem
      | BBitAnd => arith Z.land
      | BBitOr => arith Z.lor
      | BBitXor => arith Z.lxor
      | BEq => ret (VBool (Z.eqb x y))
      | BNe => ret (VBool (negb (Z.eqb x y)))
      | BLt => ret (VBool (Z.ltb x y))
      | BLe => ret (VBool (Z.leb x y))
      | BGt => ret (VBool (Z.ltb y x))
      | BGe => ret (VBool (Z.leb y x))
      | _ => fail "binary operator outside the fragment"
      end
  | VBool p, VBool q =>
      match op with
      | BEq => ret (VBool (Bool.eqb p q))
      | BNe => ret (VBool (negb (Bool.eqb p q)))
      | BBitAnd => ret (VBool (andb p q))
      | BBitOr => ret (VBool (orb p q))
      | BBitXor => ret (VBool (xorb p q))
      | _ => fail "boolean operator outside the fragment"
      end
  | _, _ => fail "operands outside the fragment"
  end.

Definition denote_unop (dst : ty) (op : un_op) (v : runtime_value)
    : M runtime_value :=
  match op, v with
  | UNot, VBool b => ret (VBool (negb b))
  | UNeg, VBits _ z =>
      match bits_of dst with
      | Some (w, s) => ret (VBits w (wrap w s (Z.opp z)))
      | None => fail "negation into a non-integer destination"
      end
  | UNot, VBits _ z =>
      match bits_of dst with
      | Some (w, s) => ret (VBits w (wrap w s (Z.lnot z)))
      | None => fail "complement into a non-integer destination"
      end
  | _, _ => fail "unary operator outside the fragment"
  end.

Definition denote_rvalue (env : layout_env) (dst : ty) (r : rvalue) : M runtime_value :=
  match r with
  | RUse o _ => denote_operand env o
  | RBinaryOp op a b =>
      x <- denote_operand env a ;;
      y <- denote_operand env b ;;
      denote_binop dst op x y
  | RUnaryOp op o => v <- denote_operand env o ;; denote_unop dst op v
  | RRef _ _ p | RRawPtr _ p =>
      fun st => match address_of_place_with_layouts env p st with
                | Some v => Ok v st
                | None => Unmodelled "address of place"
                end
  | RAggregate AgTuple fs =>
      (fix go (os : list operand) (acc : list runtime_value) : M runtime_value :=
         match os with
         | [] => ret (VTuple (rev acc))
         | o :: rest => v <- denote_operand env o ;; go rest (v :: acc)
         end) fs []
  | _ => fail "rvalue outside the fragment"
  end.

Definition local_ty (b : body) (n : nat) : ty :=
  match nth_error (bd_locals b) n with
  | Some d => ld_ty d
  | None => TError "no such local"
  end.

Definition denote_statement (env : layout_env) (b : body) (s : statement) : M unit :=
  match st_kind s with
  | SAssign p r =>
      v <- denote_rvalue env (local_ty b (pl_local p)) r ;;
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
  | SFakeRead _ _ | SAscribeUserType _ _ _ | SPlaceMention _
  | SNop | SConstEvalCounter | SCoverage _
  | SBackwardIncompatibleDropHint _ _ => ret tt
  | _ => fail "statement outside the fragment"
  end.

Fixpoint denote_statements (env : layout_env) (b : body) (ss : list statement) : M unit :=
  match ss with
  | [] => ret tt
  | s :: rest => denote_statement env b s ;;; denote_statements env b rest
  end.

Inductive result :=
  | Returned (v : runtime_value)
  | Panicked
  | Unwound.

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

Definition denote_terminator (env : layout_env) (b : body) (t : terminator) : M (block_id + result) :=
  match tm_kind t with
  | TGoto n => ret (inl n)
  | TReturn => v <- read env (Place 0 []) ;; ret (inr (Returned v))
  | TSwitchInt d ts o =>
      v <- denote_operand env d ;;
      match scalar_of v with
      | Some z => ret (inl (switch_target z ts o))
      | None => fail "switchInt on a non-scalar"
      end
  | TAssert c expected _ target _ =>
      v <- denote_operand env c ;;
      match v with
      | VBool bb => if Bool.eqb bb expected then ret (inl target)
                    else ret (inr Panicked)
      | _ => fail "assert on a non-boolean"
      end
  | TDrop p target _ _ _ =>
      fun st =>
        match read_place_result_with_layouts env p st with
        | AccessOk _ =>
            match deinitialize_place_with_layouts env p st with
            | Some st' => Ok (inl target) st'
            | None => Unmodelled "deinitialise at drop"
            end
        | AccessUb UbReadUninitialized => Ok (inl target) st
        | AccessUb r => Ub r
        | AccessFail => Unmodelled "read place at drop"
        end
  | TFalseEdge real _ => ret (inl real)
  | TFalseUnwind real _ => ret (inl real)
  | TUnreachable => raise UbReachedUnreachable
  | TUnwindResume => ret (inr Unwound)
  | _ => fail "terminator outside the fragment"
  end.

Definition find_block (b : body) (n : block_id) : option basic_block :=
  find (fun blk => Nat.eqb (bb_id blk) n) (bd_blocks b).

Definition denote_block (env : layout_env) (b : body) (n : block_id) : M (block_id + result) :=
  match find_block b n with
  | None => fail "no such block"
  | Some blk =>
      denote_statements env b (bb_stmts blk) ;;;
      denote_terminator env b (bb_term blk)
  end.

Definition denote_body (fuel : nat) (b : body) : M result :=
  iter fuel (denote_block (layouts_of_body b) b) 0.

Fixpoint args_match (b : body) (i : nat) (args : list runtime_value) : bool :=
  match args with
  | [] => true
  | v :: rest =>
      match nth_error (bd_locals b) (S i) with
      | Some d => shape_matches_ty (shape_of_value v) (ld_ty d) && args_match b (S i) rest
      | None => false
      end
  end.

Definition entry_state (b : body) (args : list runtime_value) : prog_state :=
  local_state
    (Uninit ::
     map (fun i => match nth_error args i with
                   | Some v => Init v
                   | None => Uninit
                   end)
         (seq 0 (bd_arg_count b))
     ++ repeat Uninit (length (bd_locals b) - S (bd_arg_count b))).

Definition run (fuel : nat) (b : body) (args : list runtime_value) : outcome result :=
  if negb (Nat.eqb (length args) (bd_arg_count b))
  then Mismatch "wrong number of arguments"
  else if negb (args_match b 0 args)
  then Mismatch "argument does not match the declared type"
  else denote_body fuel b (entry_state b args).

Definition run_at (fuel : nat) (b : body) (targs : list garg)
    (args : list runtime_value) : outcome result :=
  run fuel (subst_body targs b) args.

Inductive answer :=
  | ARet (v : runtime_value)
  | APanic
  | AUnwind
  | AUb (reason : ub_reason)
  | AUnmodelled (what : string)
  | AMismatch (what : string)
  | AFuel.

Definition answer_of (o : outcome result) : answer :=
  match o with
  | Ok (Returned v) _ => ARet v
  | Ok Panicked _ => APanic
  | Ok Unwound _ => AUnwind
  | Ub r => AUb r
  | Unmodelled w => AUnmodelled w
  | Mismatch w => AMismatch w
  | OutOfFuel => AFuel
  end.

Definition eval (fuel : nat) (b : body) (args : list runtime_value) : answer :=
  answer_of (run fuel b args).

Definition eval_at (fuel : nat) (b : body) (targs : list garg)
    (args : list runtime_value) : answer :=
  answer_of (run_at fuel b targs args).

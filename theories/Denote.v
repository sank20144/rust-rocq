From RustRocq Require Import Syntax Layout Memory Subst LayoutAlg.
From Stdlib Require Import String List ZArith Lia.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope nat_scope.

CoInductive delay (A : Type) : Type :=
  | Now (a : A)
  | Later (d : delay A).
Arguments Now {A} _.
Arguments Later {A} _.

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

CoFixpoint drive {L R} (step : L -> M (L + R)) (l : L) (st : prog_state)
    : delay (outcome R) :=
  match step l st with
  | Ok (inl l') st' => Later (drive step l' st')
  | Ok (inr r) st' => Now (Ok r st')
  | Ub p => Now (Ub p)
  | Unmodelled w => Now (Unmodelled w)
  | Mismatch w => Now (Mismatch w)
  end.

Inductive Terminates {A} : delay A -> A -> Prop :=
  | TNow : forall a, Terminates (Now a) a
  | TLater : forall d a, Terminates d a -> Terminates (Later d) a.

CoInductive Diverges {A} : delay A -> Prop :=
  | DLater : forall d, Diverges d -> Diverges (Later d).

Definition layouts_of_body `{Alg : LayoutAlg} (adts : list adt_def) (b : body)
    : layout_env :=
  layout_env_of adts (map ld_ty (bd_locals b)).

Definition read (env : layout_env) (p : place) : M runtime_value :=
  fun st => of_access "read place" (read_place_result_with_layouts env p st) st.

Definition write (env : layout_env) (p : place) (v : runtime_value) : M unit :=
  fun st => match write_place_with_layouts env p v st with
            | Some st' => Ok tt st'
            | None => Unmodelled "write place"
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

Definition const_value (t : ty) (v : const_value) : M runtime_value :=
  match v, t with
  | CvScalar (ScInt z _), TBool => ret (VBool (negb (Z.eqb z 0%Z)))
  | CvScalar (ScInt z _), TChar => ret (VChar z)
  | CvScalar (ScInt z _), TInt w => ret (VBits w (wrap w true z))
  | CvScalar (ScInt z _), TUint w => ret (VBits w (wrap w false z))
  | CvZeroSized, _ => ret VUnit
  | _, _ => fail "constant outside the fragment"
  end.

Definition denote_const (c : const_op) : M runtime_value :=
  match co_const c with
  | KVal v t => const_value t v
  | KTy t (CValue _ z) => const_value t (CvScalar (ScInt z 0))
  | _ => fail "unevaluated constant"
  end.

Definition denote_operand (env : layout_env) (o : operand) : M runtime_value :=
  match o with
  | OCopy p => read env p
  | OMove p =>
      v <- read env p ;;
      fun st => match deinitialize_place_with_layouts env p st with
                | Some st' => Ok v st'
                | None => Unmodelled "deinitialise at move"
                end
  | OConst c => denote_const c
  | ORuntimeCheck _ => ret (VBool true)
  end.

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

Fixpoint denote_operands (env : layout_env) (os : list operand)
    : M (list runtime_value) :=
  match os with
  | [] => ret []
  | o :: rest =>
      v <- denote_operand env o ;;
      vs <- denote_operands env rest ;;
      ret (v :: vs)
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
      vs <- denote_operands env fs ;; ret (VTuple vs)
  | RAggregate (AgAdt path v _ None) fs =>
      vs <- denote_operands env fs ;; ret (VAdt path v vs)
  | RAggregate (AgAdt _ _ _ (Some _)) _ => fail "union aggregate"
  | RDiscriminant p =>
      v <- read env p ;;
      match v with
      | VAdt _ k _ =>
          match bits_of dst with
          | Some (w, _) => ret (VBits w (Z.of_nat k))
          | None => fail "discriminant into a non-integer destination"
          end
      | _ => fail "discriminant of a non-enum value"
      end
  | _ => fail "rvalue outside the fragment"
  end.

Definition local_ty (b : body) (n : nat) : ty :=
  match nth_error (bd_locals b) n with
  | Some d => ld_ty d
  | None => TError "no such local"
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
  | SSetDiscriminant p v =>
      cur <- read env p ;;
      match cur with
      | VAdt d _ fs => write env p (VAdt d v fs)
      | _ => fail "set discriminant on a non-enum value"
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

Definition oracle : Type := name -> list garg -> list runtime_value -> M result.

Definition no_models : oracle := fun f _ _ => fail (String.append "no body for " f).

Record program := MkProgram {
  pg_adts : list adt_def;
  pg_bodies : list body;
  pg_impls : list impl_def;
  pg_ext : oracle;
}.

Definition only_adts (adts : list adt_def) : program := MkProgram adts [] [] no_models.

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
      vs <- denote_operands env args ;;
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
        | CalleeModel g gargs =>
            match pg_ext P g gargs vs st with
            | Ok (Returned v) st' =>
                (t <- return_to env dest target v ;; ret (Goto t))
                  (state_with_locals st' (state_locals st))
            | Ok r st' => Ok (Finish r) (state_with_locals st' (state_locals st))
            | Ub r => Ub r
            | Unmodelled w => Unmodelled w
            | Mismatch w => Mismatch w
            end
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
      v <- denote_operand env d ;;
      match scalar_of v with
      | Some z => ret (Goto (switch_target z ts o))
      | None => fail "switchInt on a non-scalar"
      end
  | TAssert c expected _ target _ =>
      v <- denote_operand env c ;;
      match v with
      | VBool bb => if Bool.eqb bb expected then ret (Goto target)
                    else ret (Finish Panicked)
      | _ => fail "assert on a non-boolean"
      end
  | TDrop p target _ _ _ =>
      fun st =>
        match read_place_result_with_layouts env p st with
        | AccessOk _ =>
            match deinitialize_place_with_layouts env p st with
            | Some st' => Ok (Goto target) st'
            | None => Unmodelled "deinitialise at drop"
            end
        | AccessUb UbReadUninitialized => Ok (Goto target) st
        | AccessUb r => Ub r
        | AccessFail => Unmodelled "read place at drop"
        end
  | TCall func args dest target _ _ _ => denote_call P env b func args dest target
  | TFalseEdge real _ => ret (Goto real)
  | TFalseUnwind real _ => ret (Goto real)
  | TUnreachable => raise UbReachedUnreachable
  | TUnwindResume => ret (Finish Unwound)
  | _ => fail "terminator outside the fragment"
  end.

Definition find_block (b : body) (n : block_id) : option basic_block :=
  find (fun blk => Nat.eqb (bb_id blk) n) (bd_blocks b).

Definition denote_block `{Alg : LayoutAlg} (P : program) (env : layout_env) (b : body)
    (n : block_id) : M control :=
  match find_block b n with
  | None => fail "no such block"
  | Some blk =>
      denote_statements env b (bb_stmts blk) ;;;
      denote_terminator P env b (bb_term blk)
  end.

Record frame := Frame {
  fr_body : body;
  fr_env : layout_env;
  fr_locals : list local_storage;
  fr_dest : place;
  fr_target : option block_id;
}.

Record config := Config {
  cf_body : body;
  cf_env : layout_env;
  cf_block : block_id;
  cf_stack : list frame;
}.

Definition restore (locals : list local_storage) : M unit :=
  fun st => Ok tt (state_with_locals st locals).

Fixpoint finish (stack : list frame) (r : result) : M (config + result) :=
  match stack with
  | [] => ret (inr r)
  | fr :: rest =>
      restore (fr_locals fr) ;;;
      match r with
      | Returned v =>
          t <- return_to (fr_env fr) (fr_dest fr) (fr_target fr) v ;;
          ret (inl (Config (fr_body fr) (fr_env fr) t rest))
      | Panicked | Unwound => finish rest r
      end
  end.

Definition step `{Alg : LayoutAlg} (P : program) (c : config) : M (config + result) :=
  k <- denote_block P (cf_env c) (cf_body c) (cf_block c) ;;
  match k with
  | Goto n => ret (inl (Config (cf_body c) (cf_env c) n (cf_stack c)))
  | Enter callee env saved dest target =>
      ret (inl (Config callee env 0
                  (Frame (cf_body c) (cf_env c) saved dest target :: cf_stack c)))
  | Finish r => finish (cf_stack c) r
  end.

Definition exec `{Alg : LayoutAlg} (P : program) (c : config) (st : prog_state)
    : delay (outcome result) :=
  drive (step P) c st.

Definition start `{Alg : LayoutAlg} (P : program) (b : body) : config :=
  Config b (layouts_of_body (pg_adts P) b) 0 [].

Definition run_with `{Alg : LayoutAlg} (P : program) (b : body) (memory : memory_state)
    (args : list runtime_value) : delay (outcome result) :=
  match check_args b args with
  | Some why => Now (Mismatch why)
  | None =>
      match entry_state_from (cf_env (start P b)) b memory args with
      | Some st => exec P (start P b) st
      | None => Now (Unmodelled "allocate the frame at entry")
      end
  end.

Definition run_from `{Alg : LayoutAlg} (adts : list adt_def) (b : body)
    (memory : memory_state) (args : list runtime_value) : delay (outcome result) :=
  run_with (only_adts adts) b memory args.

Definition run_in `{Alg : LayoutAlg} (adts : list adt_def) (b : body) (args : list runtime_value)
    : delay (outcome result) :=
  run_from adts b [] args.

Definition run `{Alg : LayoutAlg} (b : body) (args : list runtime_value) : delay (outcome result) :=
  run_in [] b args.

Definition run_at `{Alg : LayoutAlg} (b : body) (targs : list garg)
    (args : list runtime_value) : delay (outcome result) :=
  run (subst_body targs b) args.

Fixpoint peek {A} (n : nat) (d : delay A) : option A :=
  match n, d with
  | _, Now a => Some a
  | S k, Later d' => peek k d'
  | 0, Later _ => None
  end.

Lemma peek_terminates {A} : forall n (d : delay A) a,
  peek n d = Some a -> Terminates d a.
Proof.
  induction n as [|n IH]; intros d a H; destruct d; cbn in H.
  - injection H; intros; subst; constructor.
  - discriminate.
  - injection H; intros; subst; constructor.
  - constructor. apply IH. exact H.
Qed.

Theorem terminates_deterministic {A} : forall (d : delay A) a a',
  Terminates d a -> Terminates d a' -> a = a'.
Proof.
  intros d a a' H. revert a'.
  induction H as [x|d x _ IH]; intros a' H'; inversion H'; subst; auto.
Qed.

Theorem not_both {A} : forall (d : delay A) a, Terminates d a -> ~ Diverges d.
Proof.
  intros d a H. induction H as [x|d x _ IH]; intros C; inversion C; auto.
Qed.

Definition frob {A} (d : delay A) : delay A :=
  match d with Now a => Now a | Later d' => Later d' end.

Lemma frob_eq {A} (d : delay A) : d = frob d.
Proof. destruct d; reflexivity. Qed.

Definition after_step {L R} (step : L -> M (L + R)) (o : outcome (L + R))
    : delay (outcome R) :=
  match o with
  | Ok (inl l) st => Later (drive step l st)
  | Ok (inr r) st => Now (Ok r st)
  | Ub p => Now (Ub p)
  | Unmodelled w => Now (Unmodelled w)
  | Mismatch w => Now (Mismatch w)
  end.

Lemma drive_eq {L R} (step : L -> M (L + R)) l st :
  drive step l st = after_step step (step l st).
Proof.
  rewrite (frob_eq (drive step l st)). simpl.
  destruct (step l st) as [[l'|r] st'| | |]; reflexivity.
Qed.

Definition with_stack (c : config) (rest : list frame) : config :=
  Config (cf_body c) (cf_env c) (cf_block c) (cf_stack c ++ rest).

Definition lift (rest : list frame) (o : outcome (config + result))
    : outcome (config + result) :=
  match o with
  | Ok (inl c) st => Ok (inl (with_stack c rest)) st
  | Ok (inr r) st => finish rest r st
  | Ub p => Ub p
  | Unmodelled w => Unmodelled w
  | Mismatch w => Mismatch w
  end.

Definition resume `{Alg : LayoutAlg} (P : program) (rest : list frame) (o : outcome result)
    : delay (outcome result) :=
  match o with
  | Ok r st => after_step (step P) (finish rest r st)
  | Ub p => Now (Ub p)
  | Unmodelled w => Now (Unmodelled w)
  | Mismatch w => Now (Mismatch w)
  end.

Lemma finish_app : forall s rest r st,
  finish (s ++ rest) r st = lift rest (finish s r st).
Proof.
  induction s as [|fr s IH]; intros rest r st; [reflexivity|].
  cbn. unfold bind, restore.
  destruct r as [v| |]; [|apply IH|apply IH].
  unfold return_to. destruct (fr_target fr); [|reflexivity].
  unfold bind, write.
  destruct (write_place_with_layouts (fr_env fr) (fr_dest fr) v
              (state_with_locals st (fr_locals fr))); reflexivity.
Qed.

Lemma step_app `{Alg : LayoutAlg} (P : program) : forall c rest st,
  step P (with_stack c rest) st = lift rest (step P c st).
Proof.
  intros c rest st. unfold step, bind. cbn [cf_body cf_env cf_block cf_stack with_stack].
  destruct (denote_block P (cf_env c) (cf_body c) (cf_block c) st)
    as [k st'| | |]; try reflexivity.
  destruct k; try reflexivity. apply finish_app.
Qed.

Theorem stack_decomposition `{Alg : LayoutAlg} (P : program) :
  forall c rest st o,
    Terminates (exec P (with_stack c rest) st) o <->
    exists o1, Terminates (exec P c st) o1 /\ Terminates (resume P rest o1) o.
Proof.
  intros c rest st o. split.
  - intros H. remember (exec P (with_stack c rest) st) as d eqn:Hd.
    revert c st Hd. induction H as [a|d a H IH]; intros c st Hd;
      unfold exec in Hd; rewrite drive_eq, step_app in Hd;
      destruct (step P c st) as [[c'|r] st'| p | w | w] eqn:E; cbn in Hd;
      try discriminate.
    + exists (Ok r st'). split.
      * unfold exec. rewrite drive_eq, E. constructor.
      * cbn. rewrite <- Hd. constructor.
    + exists (Ub p). injection Hd as ->. split; [|constructor].
      unfold exec. rewrite drive_eq, E. constructor.
    + exists (Unmodelled w). injection Hd as ->. split; [|constructor].
      unfold exec. rewrite drive_eq, E. constructor.
    + exists (Mismatch w). injection Hd as ->. split; [|constructor].
      unfold exec. rewrite drive_eq, E. constructor.
    + injection Hd as Hd. destruct (IH c' st' Hd) as [o1 [H1 H2]].
      exists o1. split; [|exact H2].
      unfold exec. rewrite drive_eq, E. constructor. exact H1.
    + exists (Ok r st'). split.
      * unfold exec. rewrite drive_eq, E. constructor.
      * cbn. rewrite <- Hd. constructor. exact H.
  - intros [o1 [H1 H2]]. revert H2. remember (exec P c st) as d eqn:Hd.
    revert c st Hd. induction H1 as [a|d a H IH]; intros c st Hd H2;
      unfold exec in Hd; rewrite drive_eq in Hd;
      destruct (step P c st) as [[c'|r] st'| p | w | w] eqn:E; cbn in Hd;
      try discriminate; unfold exec; rewrite drive_eq, step_app, E; cbn.
    + injection Hd as ->. exact H2.
    + injection Hd as ->. inversion H2; subst. constructor.
    + injection Hd as ->. inversion H2; subst. constructor.
    + injection Hd as ->. inversion H2; subst. constructor.
    + injection Hd as Hd. constructor. exact (IH c' st' Hd H2).
Qed.

Corollary call_decomposition `{Alg : LayoutAlg} (P : program) :
  forall callee env fr stack st o,
    Terminates (exec P (Config callee env 0 (fr :: stack)) st) o <->
    exists o1, Terminates (exec P (Config callee env 0 []) st) o1
      /\ Terminates (resume P (fr :: stack) o1) o.
Proof.
  intros callee env fr stack st o.
  exact (stack_decomposition P (Config callee env 0 []) (fr :: stack) st o).
Qed.

Fixpoint advance {L R} (step : L -> M (L + R)) (n : nat) (l : L) (st : prog_state)
    : option (L * prog_state) :=
  match n with
  | 0 => Some (l, st)
  | S k =>
      match step l st with
      | Ok (inl l') st' => advance step k l' st'
      | _ => None
      end
  end.

Lemma advance_add {L R} (step : L -> M (L + R)) : forall a b l st,
  advance step (a + b) l st =
  match advance step a l st with
  | Some (l', st') => advance step b l' st'
  | None => None
  end.
Proof.
  induction a as [|a IH]; intros b l st; [reflexivity|].
  cbn. destruct (step l st) as [[l'|r] st'| | |]; try reflexivity. apply IH.
Qed.

Lemma diverges_invariant {L R} (step : L -> M (L + R)) (Inv : L -> prog_state -> Prop) :
  (forall l st, Inv l st -> exists l' st', step l st = Ok (inl l') st' /\ Inv l' st') ->
  forall l st, Inv l st -> Diverges (drive step l st).
Proof.
  intros Hstep. cofix CIH. intros l st Hinv.
  destruct (Hstep l st Hinv) as [l' [st' [E Hinv']]].
  rewrite (drive_eq step l st), E. constructor. exact (CIH l' st' Hinv').
Qed.

Lemma diverges_after {L R} (step : L -> M (L + R)) : forall n l st l' st',
  advance step n l st = Some (l', st') ->
  Diverges (drive step l' st') -> Diverges (drive step l st).
Proof.
  induction n as [|n IH]; intros l st l' st' H Hd; cbn in H.
  - injection H as <- <-. exact Hd.
  - destruct (step l st) as [[l1|r] st1| | |] eqn:E; try discriminate.
    rewrite drive_eq, E. constructor. exact (IH l1 st1 l' st' H Hd).
Qed.

Lemma diverges_by_cycle {L R} (step : L -> M (L + R)) (n k : nat) l st :
  match advance step n l st with
  | Some (l', st') => advance step (S k) l' st' = Some (l', st')
  | None => False
  end -> Diverges (drive step l st).
Proof.
  destruct (advance step n l st) as [[l0 st0]|] eqn:Hn; [|contradiction].
  intros Hcycle. apply (diverges_after step n l st l0 st0 Hn).
  apply (diverges_invariant step
           (fun l' st' => exists j, j <= k /\ advance step j l0 st0 = Some (l', st'))).
  - intros l' st' [j [Hj Hadv]].
    assert (Hsplit : S k = j + S (k - j)) by lia.
    pose proof Hcycle as Hc. rewrite Hsplit, advance_add, Hadv in Hc. cbn in Hc.
    destruct (step l' st') as [[l''|r] st''| | |] eqn:E; try discriminate.
    exists l'', st''. split; [reflexivity|].
    destruct (Nat.eq_dec j k) as [->|Hne].
    + rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as -> ->.
      exists 0. split; [lia | reflexivity].
    + exists (S j). split; [lia|].
      replace (S j) with (j + 1) by apply Nat.add_1_r.
      rewrite advance_add, Hadv. cbn. rewrite E. reflexivity.
  - exists 0. split; [lia | reflexivity].
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
  rewrite (terminates_deterministic _ _ _ Ht Ht') in Ha. congruence.
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
  rewrite (terminates_deterministic _ _ _ Ht Ht') in Ha, Hs. split; congruence.
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

Lemma run_with_diverges `{Alg : LayoutAlg} (P : program) (n k : nat) :
  forall b memory args,
    match check_args b args with
    | Some _ => False
    | None =>
        match entry_state_from (cf_env (start P b)) b memory args with
        | Some st =>
            match advance (step P) n (start P b) st with
            | Some (c, st') => advance (step P) (S k) c st' = Some (c, st')
            | None => False
            end
        | None => False
        end
    end ->
    Diverges (run_with P b memory args).
Proof.
  intros b memory args H. unfold run_with.
  destruct (check_args b args); [contradiction|].
  destruct (entry_state_from (cf_env (start P b)) b memory args) as [st|]; [|contradiction].
  exact (diverges_by_cycle (step P) n k (start P b) st H).
Qed.

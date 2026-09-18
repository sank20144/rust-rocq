From RustRocq Require Import Syntax LayoutAlg Memory Denote.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition partial_model : Type :=
  list adt_def -> name -> list garg -> list runtime_value -> option (M result).

Fixpoint models (ms : list partial_model) : model :=
  fun adts f targs vs =>
    match ms with
    | [] => no_model adts f targs vs
    | m :: rest =>
        match m adts f targs vs with
        | Some r => r
        | None => models rest adts f targs vs
        end
    end.

Definition returned (v : runtime_value) : M result := ret (Returned v).

Definition panics : M result := ret Panicked.

Definition phantom : runtime_value := VAdt "core::marker::PhantomData" 0 [].

Definition u64_limit : Z := (2 ^ 64)%Z.

Definition usize_limit : Z := (2 ^ 64)%Z.

Definition HM (A : Type) : Type := prog_state -> option (outcome (A + result)).

Definition hret {A} (a : A) : HM A := fun st => Some (Ok (inl a) st).

Definition hbind {A B} (m : HM A) (k : A -> HM B) : HM B :=
  fun st =>
    match m st with
    | Some (Ok (inl a) st') => k a st'
    | Some (Ok (inr r) st') => Some (Ok (inr r) st')
    | Some (Ub r) => Some (Ub r)
    | Some (Unmodelled w) => Some (Unmodelled w)
    | Some (Mismatch w) => Some (Mismatch w)
    | None => None
    end.

Definition hlift {A} (m : M A) : HM A :=
  fun st =>
    match m st with
    | Ok a st' => Some (Ok (inl a) st')
    | Ub r => Some (Ub r)
    | Unmodelled w => Some (Unmodelled w)
    | Mismatch w => Some (Mismatch w)
    end.

Definition hfail {A} (w : string) : HM A := fun _ => Some (Unmodelled w).

Definition hcall (cb : call_back) (f : name) (targs : list garg) (args : list runtime_value)
    : HM runtime_value :=
  fun st =>
    match cb f targs args st with
    | Some (Ok (Returned v) st') => Some (Ok (inl v) st')
    | Some (Ok r st') => Some (Ok (inr r) st')
    | Some (Ub r) => Some (Ub r)
    | Some (Unmodelled w) => Some (Unmodelled w)
    | Some (Mismatch w) => Some (Mismatch w)
    | None => None
    end.

Definition hresult (m : HM runtime_value) : prog_state -> option (outcome result) :=
  fun st =>
    match m st with
    | Some (Ok (inl v) st') => Some (Ok (Returned v) st')
    | Some (Ok (inr r) st') => Some (Ok r st')
    | Some (Ub r) => Some (Ub r)
    | Some (Unmodelled w) => Some (Unmodelled w)
    | Some (Mismatch w) => Some (Mismatch w)
    | None => None
    end.

Definition hmono {A} (m : call_back -> HM A) : Prop :=
  forall c1 c2, callback_le c1 c2 -> forall st o, m c1 st = Some o -> m c2 st = Some o.

Lemma hret_mono {A} (a : A) : hmono (fun _ => hret a).
Proof. intros c1 c2 _ st o H. exact H. Qed.

Lemma hfail_mono {A} (w : string) : hmono (fun _ => @hfail A w).
Proof. intros c1 c2 _ st o H. exact H. Qed.

Lemma hconst_mono {A} (m : HM A) : hmono (fun _ => m).
Proof. intros c1 c2 _ st o H. exact H. Qed.

Lemma hcall_mono f targs args : hmono (fun cb => hcall cb f targs args).
Proof.
  intros c1 c2 Hle st o H. unfold hcall in *.
  destruct (c1 f targs args st) as [o1|] eqn:E; [|discriminate].
  rewrite (Hle _ _ _ _ _ E). exact H.
Qed.

Lemma hbind_mono {A B} (m : call_back -> HM A) (k : call_back -> A -> HM B) :
  hmono m -> (forall a, hmono (fun cb => k cb a)) -> hmono (fun cb => hbind (m cb) (k cb)).
Proof.
  intros Hm Hk c1 c2 Hle st o H. unfold hbind in *.
  destruct (m c1 st) as [o1|] eqn:E; [|discriminate].
  rewrite (Hm c1 c2 Hle st o1 E).
  destruct o1 as [[a|r] st'| | |]; try exact H.
  exact (Hk a c1 c2 Hle st' o H).
Qed.

Lemma hresult_mono (m : call_back -> HM runtime_value) :
  hmono m -> forall c1 c2, callback_le c1 c2 ->
  forall st o, hresult (m c1) st = Some o -> hresult (m c2) st = Some o.
Proof.
  intros Hm c1 c2 Hle st o H. unfold hresult in *.
  destruct (m c1 st) as [o1|] eqn:E; [|discriminate].
  rewrite (Hm c1 c2 Hle st o1 E). exact H.
Qed.

Section Pointers.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition read_arg (t : ty) (v : runtime_value) : M runtime_value :=
    match v with
    | VPtr p =>
        observe "read through a model's argument" (fun st =>
          read_pointer adts (state_memory st) t p)
    | _ => fail "a model expected a pointer argument"
    end.

  Definition write_arg (t : ty) (p v : runtime_value) : M unit :=
    match p with
    | VPtr ptr =>
        change "write through a model's argument" (fun st =>
          m <-? write_pointer adts (state_memory st) t ptr v ;;
          AccessOk (state_with_memory st m))
    | _ => fail "a model expected a pointer argument"
    end.

  Definition alloc_temp (t : ty) (v : runtime_value) : HM runtime_value :=
    fun st =>
      match allocate_value adts (state_memory st) t v with
      | Some (id, memory) => Some (Ok (inl (VPointer id 0)) (state_with_memory st memory))
      | None => Some (Unmodelled "allocate a model's temporary")
      end.

End Pointers.

Definition free_temp (p : runtime_value) : HM unit :=
  fun st =>
    match p with
    | VPtr (PointerValue (ProvenanceAllocation id) _ _) =>
        match kill_allocation (state_memory st) id with
        | Some memory => Some (Ok (inl tt) (state_with_memory st memory))
        | None => Some (Unmodelled "free a model's temporary")
        end
    | _ => Some (Unmodelled "free a model's temporary")
    end.

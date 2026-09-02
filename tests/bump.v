From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import bump.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Ltac by_running :=
  match goal with
  | |- ?l = _ =>
      let l' := eval vm_compute in l in
      transitivity l'; [vm_compute; reflexivity | reflexivity]
  end.

Definition holding (z : Z) : memory_state := state_memory (local_state [Init (VBits W32 z)]).

Definition to_it : runtime_value := VPointer (ShapeBits W32) 0 0.

Definition target_in (st : option prog_state) : access_result runtime_value :=
  match st with
  | Some st => read_allocation_result_with_layouts [] (state_memory st) 0 0 (ShapeBits W32)
  | None => AccessFail
  end.

Example bump_adds_one_through_the_reference :
  exists st, MeansFrom [] bump (holding 41) [to_it] (ARet VUnit) st
    /\ target_in st = AccessOk (VBits W32 42).
Proof.
  eexists. split.
  - apply (means_from_within [] 40). by_running.
  - vm_compute. reflexivity.
Qed.

Example bump_at_the_maximum_panics_and_leaves_the_target_alone :
  exists st, MeansFrom [] bump (holding 4294967295) [to_it] APanic st
    /\ target_in st = AccessOk (VBits W32 4294967295).
Proof.
  eexists. split.
  - apply (means_from_within [] 40). by_running.
  - vm_compute. reflexivity.
Qed.

Example without_a_starting_memory_the_reference_has_no_target :
  Means bump [to_it] (AUnmodelled "allocate the frame at entry").
Proof. apply (means_within 40). vm_compute. reflexivity. Qed.

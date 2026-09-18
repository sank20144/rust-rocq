From RustRocq Require Import Syntax Memory Denote.
From Generated Require Import drops.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition P : program := only_adts adts.

Example a_value_may_outlive_what_its_reference_field_points_to :
  Means P dangling_field_at_drop [] [] (ARet VUnit).
Proof. apply (means_within P 40%nat). vm_compute. reflexivity. Qed.

Example drops_of_moved_places_are_skipped :
  Means P keep [] [VAdt "Noisy" 0 [VBits W8 3]] (ARet (VAdt "Noisy" 0 [VBits W8 3])).
Proof. apply (means_within P 40%nat). vm_compute. reflexivity. Qed.

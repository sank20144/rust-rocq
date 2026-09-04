From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import drops.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Example a_value_may_outlive_what_its_reference_field_points_to :
  MeansIn adts dangling_field_at_drop [] (ARet VUnit).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example drops_of_moved_places_are_skipped :
  MeansIn adts keep [VAdt "Noisy" 0 [VBits W8 3]] (ARet (VAdt "Noisy" 0 [VBits W8 3])).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

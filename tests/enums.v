From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import enums.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition pat32 (z : Z) : runtime_value := VBits W32 (Z.modulo z (2 ^ 32)).

Example sign_of_zero :
  MeansIn adts sign [pat32 0] (ARet (VAdt "Sign" 1 [])).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example sign_of_a_positive :
  MeansIn adts sign [pat32 3] (ARet (VAdt "Sign" 2 [])).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example weight_of_neg :
  MeansIn adts weight [VAdt "Sign" 0 []] (ARet (pat32 (-1))).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example weight_of_pos :
  MeansIn adts weight [VAdt "Sign" 2 []] (ARet (VBits W32 1)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example unwrap_or_takes_the_payload :
  MeansIn adts unwrap_or [VAdt "Maybe" 1 [VBits W32 4]; VBits W32 9] (ARet (VBits W32 4)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example unwrap_or_takes_the_default :
  MeansIn adts unwrap_or [VAdt "Maybe" 0 []; VBits W32 9] (ARet (VBits W32 9)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example incr_of_just :
  MeansIn adts incr [VAdt "Maybe" 1 [VBits W32 4]] (ARet (VAdt "Maybe" 1 [VBits W32 5])).
Proof. apply (means_within_in adts 60%nat). vm_compute. reflexivity. Qed.

Example incr_of_nothing :
  MeansIn adts incr [VAdt "Maybe" 0 []] (ARet (VAdt "Maybe" 0 [])).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example a_wrong_downcast_is_ub :
  match denote_operand (only_adts []) []
          (OCopy (Place 1%nat [PDowncast None 1%nat; PField 0%nat (TUint W32)]))
          (local_state [Uninit; Init (VAdt "Maybe" 0 [])]) with
  | Ub UbInvalidEnumTag => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example a_declared_discriminant_picks_the_first_arm :
  MeansIn adts code_value [VAdt "Code" 0 []] (ARet (VBits W32 100)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example a_declared_discriminant_picks_the_second_arm :
  MeansIn adts code_value [VAdt "Code" 1 []] (ARet (VBits W32 200)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example a_negative_discriminant_matches_its_bit_pattern :
  MeansIn adts level_value [VAdt "Level" 0 []] (ARet (VBits W32 10)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

Example a_positive_discriminant_next_to_a_negative_one :
  MeansIn adts level_value [VAdt "Level" 1 []] (ARet (VBits W32 20)).
Proof. apply (means_within_in adts 40%nat). vm_compute. reflexivity. Qed.

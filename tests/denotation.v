From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import arith.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition pat32 (z : Z) : runtime_value := VBits W32 (Z.modulo z (2 ^ 32)).

Example add_two_and_three :
  eval 20 add [VBits W32 2; VBits W32 3]
  = ARet (VBits W32 5).
Proof. vm_compute. reflexivity. Qed.

Example add_is_signed :
  eval 20 add [pat32 (-5); pat32 2] = ARet (pat32 (-3)).
Proof. vm_compute. reflexivity. Qed.

Example add_overflow_panics :
  eval 20 add [VBits W32 2147483647; VBits W32 1]
  = APanic.
Proof. vm_compute. reflexivity. Qed.

Example gcd_of_twelve_and_eighteen :
  eval 120 gcd [VBits W64 12; VBits W64 18]
  = ARet (VBits W64 6).
Proof. vm_compute. reflexivity. Qed.

Example spin_never_finishes :
  eval 30 spin [VBits W64 7] = AFuel.
Proof. vm_compute. reflexivity. Qed.

Example a_generic_body_will_not_run_uninstantiated :
  eval 20 id [VBits W32 7]
  = AMismatch "argument does not match the declared type".
Proof. vm_compute. reflexivity. Qed.

Example instantiating_makes_it_run :
  eval_at 20 id [GTy (TUint W32)] [VBits W32 7] = ARet (VBits W32 7).
Proof. vm_compute. reflexivity. Qed.

Example instantiated_at_u32_still_refuses_a_bool :
  eval_at 20 id [GTy (TUint W32)] [VBool true]
  = AMismatch "argument does not match the declared type".
Proof. vm_compute. reflexivity. Qed.

Example a_monomorphic_body_refuses_the_wrong_type :
  eval 20 add [VBool true; VBits W32 3]
  = AMismatch "argument does not match the declared type".
Proof. vm_compute. reflexivity. Qed.

Example the_wrong_number_of_arguments_is_refused :
  eval 20 add [VBits W32 1] = AMismatch "wrong number of arguments".
Proof. vm_compute. reflexivity. Qed.

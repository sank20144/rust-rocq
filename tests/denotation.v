From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import arith.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Example add_two_and_three :
  eval 20 add [VBits W32 2; VBits W32 3]
  = ARet (VBits W32 5).
Proof. vm_compute. reflexivity. Qed.

Example add_is_signed :
  eval 20 add [VBits W32 4294967291; VBits W32 2]
  = ARet (VBits W32 4294967293).
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

From Vmir Require Import Layout Language.
From RustRocq Require Import Syntax Denote.
From Generated Require Import arith.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Example add_two_and_three :
  eval 20 add [VBits Layout.W32 2; VBits Layout.W32 3]
  = ARet (VBits Layout.W32 5).
Proof. vm_compute. reflexivity. Qed.

Example add_is_signed :
  eval 20 add [VBits Layout.W32 4294967291; VBits Layout.W32 2]
  = ARet (VBits Layout.W32 4294967293).
Proof. vm_compute. reflexivity. Qed.

Example add_overflow_panics :
  eval 20 add [VBits Layout.W32 2147483647; VBits Layout.W32 1]
  = APanic.
Proof. vm_compute. reflexivity. Qed.

Example gcd_of_twelve_and_eighteen :
  eval 120 gcd [VBits Layout.W64 12; VBits Layout.W64 18]
  = ARet (VBits Layout.W64 6).
Proof. vm_compute. reflexivity. Qed.

Example spin_never_finishes :
  eval 30 spin [VBits Layout.W64 7] = AFuel.
Proof. vm_compute. reflexivity. Qed.

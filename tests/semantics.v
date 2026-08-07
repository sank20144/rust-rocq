From RustRocq Require Import Syntax Eval.
From Generated Require Import arith.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Example add_two_and_three : eval_body 100 add [VInt 2; VInt 3] = Done (VInt 5).
Proof. vm_compute. reflexivity. Qed.

Example add_is_signed : eval_body 100 add [VInt (-5); VInt 2] = Done (VInt (-3)).
Proof. vm_compute. reflexivity. Qed.

Example add_overflow_is_caught :
  eval_body 100 add [VInt 2147483647; VInt 1] = Stuck "assertion failed".
Proof. vm_compute. reflexivity. Qed.

Example gcd_of_twelve_and_eighteen :
  eval_body 500 gcd [VInt 12; VInt 18] = Done (VInt 6).
Proof. vm_compute. reflexivity. Qed.

Example gcd_of_coprimes : eval_body 500 gcd [VInt 35; VInt 64] = Done (VInt 1).
Proof. vm_compute. reflexivity. Qed.

Example collatz_of_twenty_seven :
  eval_body 3000 collatz_steps [VInt 27] = Done (VInt 111).
Proof. vm_compute. reflexivity. Qed.

Example collatz_of_one_is_immediate :
  eval_body 100 collatz_steps [VInt 1] = Done (VInt 0).
Proof. vm_compute. reflexivity. Qed.

Example spin_never_finishes : eval_body 50 spin [VInt 7] = Diverged.
Proof. vm_compute. reflexivity. Qed.

Example spin_still_unfinished_with_more_fuel :
  eval_body 5000 spin [VInt 7] = Diverged.
Proof. vm_compute. reflexivity. Qed.

Example fuel_only_refines :
  eval_body 100 collatz_steps [VInt 27] = Diverged
  /\ eval_body 3000 collatz_steps [VInt 27] = Done (VInt 111)
  /\ eval_body 9000 collatz_steps [VInt 27] = Done (VInt 111).
Proof. repeat split; vm_compute; reflexivity. Qed.

Example outside_the_fragment_is_stuck :
  eval_body 100 add [VBool true; VInt 1] = Stuck "statement outside the fragment".
Proof. vm_compute. reflexivity. Qed.

From RustRocq Require Import Syntax Layout Memory Denote.
From Generated Require Import arith.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition pat32 (z : Z) : runtime_value := VBits W32 (Z.modulo z (2 ^ 32)).

Example add_two_and_three :
  Means add [VBits W32 2; VBits W32 3] (ARet (VBits W32 5)).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example add_is_signed :
  Means add [pat32 (-5); pat32 2] (ARet (pat32 (-3))).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example add_overflow_panics :
  Means add [VBits W32 2147483647; VBits W32 1] APanic.
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example gcd_of_twelve_and_eighteen :
  Means gcd [VBits W64 12; VBits W64 18] (ARet (VBits W64 6)).
Proof. apply (means_within 120%nat). vm_compute. reflexivity. Qed.

Example a_monomorphic_body_refuses_the_wrong_type :
  Means add [VBool true; VBits W32 3]
    (AMismatch "argument does not match the declared type").
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example the_wrong_number_of_arguments_is_refused :
  Means add [VBits W32 1] (AMismatch "wrong number of arguments").
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Definition one_local : prog_state := local_state [Uninit; Init (VBits W32 7)].

Example a_move_deinitialises_its_source :
  match denote_operand (only_adts []) [] (OMove (Place 1%nat [])) one_local with
  | Ok v st => (v, read_place_result_with_layouts [] (Place 1%nat []) st)
  | _ => (VUnit, AccessFail)
  end
  = (VBits W32 7, AccessUb UbReadUninitialized).
Proof. vm_compute. reflexivity. Qed.

Example a_copy_leaves_its_source_alone :
  match denote_operand (only_adts []) [] (OCopy (Place 1%nat [])) one_local with
  | Ok v st => (v, read_place_result_with_layouts [] (Place 1%nat []) st)
  | _ => (VUnit, AccessFail)
  end
  = (VBits W32 7, AccessOk (VBits W32 7)).
Proof. vm_compute. reflexivity. Qed.

Example the_return_place_is_allocated_at_entry :
  match entry_state (layouts_of_body [] add) add [VBits W32 2; VBits W32 3] with
  | Some st =>
      match nth_error (state_locals st) 0%nat with
      | Some (LocalAllocated _) => true
      | _ => false
      end
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example the_frame_is_freed_at_return :
  match peek 20%nat (run add [VBits W32 2; VBits W32 3]) with
  | Some (Ok _ st) =>
      forallb (fun s => match s with LocalAllocated _ => false | _ => true end)
              (state_locals st)
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example a_signed_comparison_puts_minus_one_below_zero :
  Means is_below [pat32 (-1); pat32 0] (ARet (VBool true)).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example a_signed_comparison_on_i8 :
  Means is_at_most [VBits W8 200; VBits W8 5] (ARet (VBool true)).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example a_switch_on_the_largest_u128 :
  Means is_max [VBits W128 (2 ^ 128 - 1)] (ARet (VBool true)).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example signed_division_rounds_towards_zero :
  Means quotient [pat32 (-7); pat32 2] (ARet (pat32 (-3))).
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example dividing_the_minimum_by_minus_one_panics :
  Means quotient [pat32 (-2147483648); pat32 (-1)] APanic.
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example dividing_by_zero_panics :
  Means quotient [pat32 7; pat32 0] APanic.
Proof. apply (means_within 20%nat). vm_compute. reflexivity. Qed.

Example the_division_operator_is_undefined_on_the_minimum_over_minus_one :
  denote_binop (TInt W32) (TInt W32) BDiv (pat32 (-2147483648)) (pat32 (-1)) (ByteState [] [])
    = Ub UbDivisionOverflow.
Proof. vm_compute. reflexivity. Qed.

Example the_remainder_operator_is_undefined_on_zero :
  denote_binop (TInt W32) (TInt W32) BRem (pat32 7) (pat32 0) (ByteState [] [])
    = Ub UbDivisionByZero.
Proof. vm_compute. reflexivity. Qed.

Example a_write_to_a_dead_local_is_undefined :
  write [] (Place 1%nat []) (VBits W32 7) (ByteState [LocalUnallocated; LocalDead] [])
    = Ub UbReadDead.
Proof. vm_compute. reflexivity. Qed.

Example the_runtime_check_operand_cannot_appear_at_this_phase :
  denote_operand (only_adts []) [] (ORuntimeCheck RcUbChecks) (ByteState [] []) = Unmodelled "ORuntimeCheck".
Proof. vm_compute. reflexivity. Qed.

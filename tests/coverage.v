From RustRocq Require Import Syntax Subst.
From Generated Require Import coverage.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition at_u32 : body := subst_body [GTy (TUint W32)] largest.

Example instantiation_consumes_the_parameter : bd_generics at_u32 = [].
Proof. reflexivity. Qed.

Example return_type_is_concrete :
  option_map ld_ty (nth_error (bd_locals at_u32) 0)
  = Some (TAdt "std::option::Option" [GTy (TUint W32)]).
Proof. reflexivity. Qed.

Example argument_type_is_concrete :
  option_map ld_ty (nth_error (bd_locals at_u32) 1)
  = Some (TRef (RVar 12) (TSlice (TUint W32)) Imm).
Proof. reflexivity. Qed.

Example bounds_are_instantiated_too :
  bd_bounds at_u32
  = [ BdTrait "std::marker::Sized" [GTy (TUint W32)]
    ; BdTrait "std::cmp::PartialOrd" [GTy (TUint W32); GTy (TUint W32)]
    ; BdTrait "std::marker::Copy" [GTy (TUint W32)]
    ].
Proof. reflexivity. Qed.

Example structure_is_preserved :
  length (bd_blocks at_u32) = length (bd_blocks largest)
  /\ bd_borrowck at_u32 = bd_borrowck largest.
Proof. split; reflexivity. Qed.

Example the_impl_table_resolves_a_bound :
  map (fun i => (ip_trait i, ip_args i)) impls
  = [("Speak", [GTy (TAdt "Dog" [])])].
Proof. reflexivity. Qed.

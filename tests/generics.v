From RustRocq Require Import Syntax Layout Memory Subst Denote.
From Generated Require Import generics.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition id_u32 : body := subst_body [GTy (TUint W32)] id.

Example instantiation_consumes_the_parameter : bd_generics id_u32 = [].
Proof. reflexivity. Qed.

Example the_argument_becomes_concrete :
  option_map ld_ty (nth_error (bd_locals id_u32) 1) = Some (TUint W32).
Proof. reflexivity. Qed.

Example control_flow_and_polonius_facts_survive :
  length (bd_blocks id_u32) = length (bd_blocks id)
  /\ bd_facts id_u32 = bd_facts id.
Proof. split; reflexivity. Qed.

Example first_takes_its_own_parameter :
  option_map ld_ty (nth_error (bd_locals (subst_body [GTy TBool; GTy (TInt W8)] first)) 1)
  = Some TBool.
Proof. reflexivity. Qed.

Example a_late_bound_lifetime_is_not_a_generic_parameter :
  bd_generics borrowed = [GpTy 0 "T"].
Proof. reflexivity. Qed.

Example the_type_parameter_is_at_index_zero :
  option_map ld_ty (nth_error (bd_locals (subst_body [GTy (TUint W64)] borrowed)) 1)
  = Some (TRef (RVar 4) (TUint W64) Imm).
Proof. reflexivity. Qed.

Example bounds_are_instantiated_too :
  bd_bounds (subst_body [GTy (TUint W32)] largest)
  = [ BdTrait "std::marker::Sized" [GTy (TUint W32)]
    ; BdTrait "std::cmp::PartialOrd" [GTy (TUint W32); GTy (TUint W32)]
    ; BdTrait "std::marker::Copy" [GTy (TUint W32)]
    ].
Proof. reflexivity. Qed.

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

Example substituting_nothing_changes_nothing : subst_body [] id = id.
Proof. reflexivity. Qed.

Example an_argument_of_the_wrong_kind_is_reported :
  subst_ty [GLifetime RStatic] (TParam 0 "T")
  = TError "generic argument kind mismatch".
Proof. reflexivity. Qed.

Example substitution_reaches_under_constructors :
  subst_ty [GTy (TInt W8)]
    (TTuple [TSlice (TParam 0 "T"); TAdt "Vec" [GTy (TParam 0 "T")]])
  = TTuple [TSlice (TInt W8); TAdt "Vec" [GTy (TInt W8)]].
Proof. reflexivity. Qed.

Example all_three_parameter_kinds_share_an_index_space :
  subst_ty [GLifetime RStatic; GTy TBool; GConst (CValue (TUint WSize) 4%Z)]
    (TRef (RParam 0 "'a") (TArray (TParam 1 "T") (CParam 2 "N")) Imm)
  = TRef RStatic (TArray TBool (CValue (TUint WSize) 4%Z)) Imm.
Proof. reflexivity. Qed.

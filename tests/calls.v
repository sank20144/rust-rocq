From RustRocq Require Import Syntax Memory Denote.
From Generated Require Import calls.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition with_models (m : model) : program :=
  MkProgram adts bodies impls (first_order m) (first_order_monotone m).

Definition P : program := with_models no_model.

Definition u32 (z : Z) : runtime_value := VBits W32 z.

Example a_call_inside_a_call :
  Means P quadruple [] [u32 3] (ARet (u32 12)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example the_largest_factorial_that_fits_in_a_u16 :
  Means P factorial [] [VBits W16 8] (ARet (VBits W16 40320)).
Proof. apply (means_within P 400). vm_compute. reflexivity. Qed.

Example an_overflow_nine_frames_deep_panics_the_whole_call :
  Means P factorial [] [VBits W16 9] APanic.
Proof. apply (means_within P 400). vm_compute. reflexivity. Qed.

Example mutual_recursion_even :
  Means P is_even [] [u32 7] (ARet (VBool false)).
Proof. apply (means_within P 400). vm_compute. reflexivity. Qed.

Example mutual_recursion_odd :
  Means P is_odd [] [u32 7] (ARet (VBool true)).
Proof. apply (means_within P 400). vm_compute. reflexivity. Qed.

Example a_callee_writes_through_a_reference_into_the_caller :
  Means P bump_twice [] [u32 5] (ARet (u32 7)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example nested_calls_that_stay_in_range :
  Means P succ_of_succ [] [VBits W8 3] (ARet (VBits W8 5)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example an_inner_call_that_overflows_panics :
  Means P succ_of_succ [] [VBits W8 254] APanic.
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example after_a_panic_the_state_holds_the_outer_locals :
  match run_with P succ_of_succ [] [VBits W8 254] 100 with
  | Some (Ok Panicked st) => length (state_locals st) = length (bd_locals succ_of_succ)
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example a_generic_callee_is_instantiated_at_the_call :
  Means P through_id [] [u32 9] (ARet (u32 9)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_generic_callee_with_a_bound :
  Means P pick_second [] [VBool true; VBool false] (ARet (VBool false)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_const_generic_callee_reads_its_parameter :
  Means P five [] [] (ARet (u32 5)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_call_repeated_in_a_loop :
  Means P double_n_times [] [u32 3; u32 4] (ARet (u32 48)).
Proof. apply (means_within P 400). vm_compute. reflexivity. Qed.

Example a_struct_is_returned_and_passed_by_value :
  Means P pair_round_trip [] [u32 3; u32 4] (ARet (u32 7)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_struct_is_changed_through_a_mutable_reference :
  Means P swapped_difference [] [u32 3; u32 10] (ARet (u32 7)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_field_is_written_from_a_nested_call :
  Means P doubled_first [] [u32 3; u32 4] (ARet (u32 10)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_callee_may_use_a_type_its_caller_never_mentions :
  Means P after_hidden_pair [] [u32 3] (ARet (u32 5)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example every_frame_is_freed_by_the_end :
  match run_with P after_hidden_pair [] [u32 3] 100 with
  | Some (Ok (Returned _) st) =>
      forallb (fun a => negb (allocation_live a)) (state_memory st) = true
      /\ length (state_locals st) = length (bd_locals after_hidden_pair)
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example a_trait_method_resolves_to_its_impl :
  Means P square_area [] [u32 3] (ARet (u32 9)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example the_impl_is_chosen_by_the_self_type :
  Means P rect_area [] [u32 3; u32 5] (ARet (u32 15)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_trait_call_in_a_generic_body_resolves_after_instantiation :
  Means P two_squares [] [u32 3; u32 4] (ARet (u32 25)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_default_method_calls_back_into_the_impl :
  Means P square_doubled [] [u32 3] (ARet (u32 18)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example an_overriding_method_wins_over_the_default :
  Means P rect_doubled [] [u32 3; u32 5] (ARet (u32 30)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_generic_impl_is_matched_against_the_call :
  Means P unwrap_u8 [] [VBits W8 7] (ARet (VBits W8 7)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example matching_binds_the_impl_parameter :
  first_some (impl_target "Get::get" [GTy (TAdt "Wrap" [GTy (TUint W8)]); GTy (TUint W8)]) impls
  = Some ("<Wrap<T> as Get<T>>::get", [GTy (TUint W8)]).
Proof. reflexivity. Qed.

Example matching_rejects_an_inconsistent_binding :
  first_some (impl_target "Get::get" [GTy (TAdt "Wrap" [GTy (TUint W8)]); GTy (TUint W16)]) impls
  = None.
Proof. reflexivity. Qed.

Example impl_parameters_come_before_the_method_parameters :
  first_some (impl_target "Choose::choose" [GTy (TAdt "Wrap" [GTy TBool]); GTy (TUint W16)])
    impls
  = Some ("<Wrap<T> as Choose>::choose", [GTy TBool; GTy (TUint W16)]).
Proof. reflexivity. Qed.

Example a_generic_method_of_a_generic_impl :
  Means P choose_first [] [VBool true; VBits W16 3; VBits W16 4] (ARet (VBits W16 3)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example the_default_body_is_used_when_no_impl_overrides_it :
  match resolve P "Area::doubled_area" [GTy (TAdt "Square" [])] with
  | CalleeBody b => bd_name b
  | CalleeModel f _ => f
  end = "Area::doubled_area".
Proof. vm_compute. reflexivity. Qed.

Example a_function_item_held_in_a_local_is_called :
  Means P through_a_local [] [u32 3] (ARet (u32 6)).
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_callee_that_is_not_a_function_item :
  match denote_call P double (OCopy (Place 1%nat [])) [] (Place 0%nat []) (Some 0%nat)
          (ByteState [] []) with
  | Unmodelled w => w
  | _ => ""
  end = "callee is not a function item".
Proof. vm_compute. reflexivity. Qed.

Example a_function_without_a_body_or_model :
  Means P larger [] [u32 3; u32 5] (AUnmodelled "no body for std::cmp::max").
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Definition max_model : model := fun adts f targs vs st =>
  if String.eqb f "std::cmp::max" then
    match vs with
    | [VBits w a; VBits _ b] => Ok (Returned (VBits w (Z.max a b))) st
    | _ => Unmodelled "max"
    end
  else no_model adts f targs vs st.

Definition swap_model : model := fun adts f targs vs st =>
  if String.eqb f "std::mem::swap" then
    match targs, vs with
    | [GTy t], [VPtr pa; VPtr pb] =>
        let m := state_memory st in
        match read_pointer adts m t pa, read_pointer adts m t pb with
        | AccessOk a, AccessOk b =>
            match write_pointer adts m t pa b with
            | AccessOk m1 =>
                match write_pointer adts m1 t pb a with
                | AccessOk m2 => Ok (Returned VUnit) (state_with_memory st m2)
                | _ => Unmodelled "swap"
                end
            | _ => Unmodelled "swap"
            end
        | _, _ => Unmodelled "swap"
        end
    | _, _ => Unmodelled "swap"
    end
  else no_model adts f targs vs st.

Definition abort_as (r : result) : model := fun adts f targs vs st =>
  if String.eqb f "std::process::abort" then Ok r st else no_model adts f targs vs st.

Definition abort_as_ub : model := fun adts f targs vs st =>
  if String.eqb f "std::process::abort" then Ub UbInvalidScalar else no_model adts f targs vs st.

Example a_model_supplies_the_result :
  Means (with_models max_model) larger [] [u32 3; u32 5] (ARet (u32 5)).
Proof. apply (means_within (with_models max_model) 100). vm_compute. reflexivity. Qed.

Example a_model_changes_memory_through_its_arguments :
  Means (with_models swap_model) exchange [] [u32 3; u32 5] (ARet (u32 5)).
Proof. apply (means_within (with_models swap_model) 100). vm_compute. reflexivity. Qed.

Example a_missing_model_two_frames_down :
  Means P call_stop [] [] (AUnmodelled "no body for std::process::abort").
Proof. apply (means_within P 100). vm_compute. reflexivity. Qed.

Example a_panic_from_a_model_reaches_the_outermost_frame :
  Means (with_models (abort_as Panicked)) call_stop [] [] APanic.
Proof. apply (means_within (with_models (abort_as Panicked)) 100). vm_compute. reflexivity. Qed.

Example an_unwind_from_a_model_reaches_the_outermost_frame :
  Means (with_models (abort_as Unwound)) call_stop [] [] AUnwind.
Proof. apply (means_within (with_models (abort_as Unwound)) 100). vm_compute. reflexivity. Qed.

Example returning_into_a_call_with_no_target_is_undefined :
  Means (with_models (abort_as (Returned VUnit))) call_stop [] [] (AUb UbReachedUnreachable).
Proof.
  apply (means_within (with_models (abort_as (Returned VUnit))) 100).
  vm_compute. reflexivity.
Qed.

Example undefined_behaviour_in_a_model_is_passed_on :
  Means (with_models abort_as_ub) call_stop [] [] (AUb UbInvalidScalar).
Proof. apply (means_within (with_models abort_as_ub) 100). vm_compute. reflexivity. Qed.

Example calling_a_function_that_loops_forever_diverges :
  Diverges (run_with P call_spin [] []).
Proof. apply (run_with_calls_cycling P call_spin [] [] 1 1). vm_compute. reflexivity. Qed.

Definition renamed (n : name) (b : body) : body :=
  Body n (bd_file b) (bd_span b) (bd_generics b) (bd_bounds b) (bd_arg_count b)
    (bd_locals b) (bd_blocks b) (bd_regions b) (bd_borrowck b).

Example a_callee_with_the_wrong_argument_type :
  Means (MkProgram adts (renamed "double" succ :: bodies) impls no_models no_models_monotone) quadruple [] [u32 3] (AMismatch "argument does not match the declared type").
Proof.
  apply (means_within (MkProgram adts (renamed "double" succ :: bodies) impls no_models no_models_monotone) 100).
  vm_compute. reflexivity.
Qed.

Example a_callee_with_the_wrong_number_of_arguments :
  Means (MkProgram adts (renamed "double" pick_second :: bodies) impls no_models no_models_monotone) quadruple [] [u32 3] (AMismatch "wrong number of arguments").
Proof.
  apply (means_within (MkProgram adts (renamed "double" pick_second :: bodies) impls no_models no_models_monotone) 100).
  vm_compute. reflexivity.
Qed.

Example without_the_program_a_call_has_no_body :
  Means (only_adts adts) quadruple [] [u32 3] (AUnmodelled "no body for double").
Proof. apply (means_within (only_adts adts) 100). vm_compute. reflexivity. Qed.

Example returning_a_trait_object_keeps_its_concrete_type :
  Means P as_debug (state_memory (local_state adts [Init (TUint W32) (u32 41)])) [VPointer 0 0]
    (ARet (VPtr (PointerValue (ProvenanceAllocation 0) 0 (PointerVTable (TUint W32))))).
Proof. apply (means_within P 10). vm_compute. reflexivity. Qed.

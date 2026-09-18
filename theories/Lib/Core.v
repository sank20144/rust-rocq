From RustRocq Require Import Syntax LayoutAlg Memory Denote Lib.Models.
From Stdlib Require Import Bool String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition option_path : name := "core::option::Option".

Definition control_flow_path : name := "core::ops::ControlFlow".

Definition none_value : runtime_value := VAdt option_path 0 [].

Definition some_value (v : runtime_value) : runtime_value := VAdt option_path 1 [v].

Definition is_option (t : ty) : bool :=
  match t with
  | TAdt p _ => String.eqb p option_path
  | _ => false
  end.

Section Core.

  Context `{Alg : LayoutAlg}.

  Definition core_model (overflow_checks : bool) : partial_model := fun adts f targs vs =>
    if String.eqb f "core::option::Option::<T>::unwrap" then
      Some match vs with
           | [VAdt p 1 [v]] => if String.eqb p option_path then returned v
                               else fail "Option::unwrap of a value that is not an option"
           | [VAdt p 0 []] => if String.eqb p option_path then panics
                              else fail "Option::unwrap of a value that is not an option"
           | _ => fail "Option::unwrap with unexpected arguments"
           end
    else if String.eqb f "core::ops::Try::branch" then
      match targs with
      | [GTy t] =>
          if is_option t then
            Some match vs with
                 | [VAdt _ 1 [v]] => returned (VAdt control_flow_path 0 [v])
                 | [VAdt _ 0 []] => returned (VAdt control_flow_path 1 [none_value])
                 | _ => fail "Try::branch of a value that is not an option"
                 end
          else None
      | _ => None
      end
    else if String.eqb f "core::ops::FromResidual::from_residual" then
      match targs with
      | [GTy t; GTy _] => if is_option t then Some (returned none_value) else None
      | _ => None
      end
    else if String.eqb f "core::ops::Sub::sub" then
      match targs, vs with
      | [GTy (TRef _ (TUint WSize) _); GTy (TRef _ (TUint WSize) _)], [x; y] =>
          Some (a <- read_arg adts (TUint WSize) x ;;
                b <- read_arg adts (TUint WSize) y ;;
                match a, b with
                | VBits _ za, VBits _ zb =>
                    if overflow_checks && Z.ltb za zb then panics
                    else returned (VBits WSize (Z.modulo (za - zb) usize_limit))
                | _, _ => fail "&usize - &usize on values that are not integers"
                end)
      | _, _ => None
      end
    else None.

End Core.

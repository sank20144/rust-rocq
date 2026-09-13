From RustRocq Require Import Syntax Layout Memory Denote Lib.Models.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition non_null_path : name := "core::ptr::NonNull".
Definition argument_path : name := "core::fmt::rt::Argument".
Definition argument_type_path : name := "core::fmt::rt::ArgumentType".
Definition arguments_path : name := "core::fmt::Arguments".

Definition thin (p : pointer_value) : pointer_value :=
  PointerValue (pointer_provenance_of p) (pointer_address p) PointerThin.

Definition non_null (pointee : value_shape) (p : pointer_value) : runtime_value :=
  VAdt non_null_path 0 [VPointerValue pointee (thin p)].

Definition debug_formatter : runtime_value :=
  VPointerValue ShapeUnit (PointerValue (ProvenanceFunction "core::fmt::Debug::fmt") 0 PointerThin).

Definition argument_value (p : pointer_value) : runtime_value :=
  VAdt argument_path 0 [VAdt argument_type_path 0 [non_null ShapeUnit p; debug_formatter; phantom]].

Definition dangling (align : Z) : pointer_value := PointerValue ProvenanceNone align PointerThin.

Definition argument_shape : value_shape :=
  ShapeAdtType (TAdt argument_path [GLifetime RErased]).

Definition fmt_model : partial_model := fun env f targs vs =>
  if String.eqb f "core::fmt::rt::Argument::<'_/#0>::new_debug" then
    Some match vs with
         | [VPointerValue _ p] => returned (argument_value p)
         | _ => fail "Argument::new_debug with unexpected arguments"
         end
  else if String.eqb f "core::fmt::Arguments::<'a/#0>::new" then
    Some match vs with
         | [VPointerValue _ template; VPointerValue _ args] =>
             returned (VAdt arguments_path 0
                         [non_null (ShapeBits W8) template; non_null argument_shape args])
         | _ => fail "Arguments::new with unexpected arguments"
         end
  else if String.eqb f "core::fmt::Arguments::<'a/#0>::from_str" then
    Some match vs with
         | [VPointerValue _ text] =>
             returned (VAdt arguments_path 0
                         [non_null (ShapeBits W8) text; non_null argument_shape (dangling 8)])
         | _ => fail "Arguments::from_str with unexpected arguments"
         end
  else if String.eqb f "core::panicking::panic_fmt" then
    Some panics
  else None.

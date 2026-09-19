From RustRocq Require Import Syntax Memory Denote Lib.Models.
From Stdlib Require Import Bool String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition non_null_path : name := "core::ptr::NonNull".
Definition argument_path : name := "core::fmt::rt::Argument".
Definition argument_type_path : name := "core::fmt::rt::ArgumentType".
Definition arguments_path : name := "core::fmt::Arguments".

Definition thin (p : pointer_value) : pointer_value :=
  PointerValue (pointer_provenance_of p) (pointer_address p) PointerThin.

Definition non_null (p : pointer_value) : runtime_value :=
  VAdt non_null_path 0 [VPtr (thin p)].

Definition debug_formatter : runtime_value :=
  VPtr (PointerValue (ProvenanceFunction "core::fmt::Debug::fmt") 0 PointerThin).

Definition argument_value (p : pointer_value) : runtime_value :=
  VAdt argument_path 0 [VAdt argument_type_path 0 [non_null p; debug_formatter; phantom]].

Definition dangling (align : Z) : pointer_value := PointerValue ProvenanceNone align PointerThin.

Definition formatted : runtime_value := VAdt "core::result::Result" 0 [VUnit].

Definition fmt_model : partial_model := fun _ f targs vs =>
  if String.eqb f "core::fmt::rt::Argument::<'_/#0>::new_debug" then
    Some match vs with
         | [VPtr p] => returned (argument_value p)
         | _ => fail "Argument::new_debug with unexpected arguments"
         end
  else if String.eqb f "core::fmt::Arguments::<'a/#0>::new" then
    Some match vs with
         | [VPtr template; VPtr args] =>
             returned (VAdt arguments_path 0
                         [non_null template; non_null args])
         | _ => fail "Arguments::new with unexpected arguments"
         end
  else if String.eqb f "core::fmt::Arguments::<'a/#0>::from_str" then
    Some match vs with
         | [VPtr text] =>
             returned (VAdt arguments_path 0
                         [non_null text; non_null (dangling 8)])
         | _ => fail "Arguments::from_str with unexpected arguments"
         end
  else if String.eqb f "core::fmt::Formatter::<'a/#0>::debug_struct_field3_finish" then
    Some match vs with
         | [_; _; _; _; _; _; _; _] => returned formatted
         | _ => fail "Formatter::debug_struct_field3_finish with unexpected arguments"
         end
  else if String.eqb f "core::panicking::panic_fmt" then
    Some panics
  else None.

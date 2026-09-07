From RustRocq Require Import Syntax Layout Memory Denote.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition partial_model : Type :=
  layout_env -> name -> list garg -> list runtime_value -> option (M result).

Fixpoint models (ms : list partial_model) : model :=
  fun env f targs vs =>
    match ms with
    | [] => no_model env f targs vs
    | m :: rest =>
        match m env f targs vs with
        | Some r => r
        | None => models rest env f targs vs
        end
    end.

Definition returned (v : runtime_value) : M result := ret (Returned v).

Definition panics : M result := ret Panicked.

Definition read_arg (env : layout_env) (v : runtime_value) : M runtime_value :=
  match v with
  | VPointerValue shape p =>
      fun st => of_access "read through a model's argument"
                  (read_through_pointer_result env shape p st) st
  | _ => fail "a model expected a pointer argument"
  end.

Definition phantom : runtime_value := VAdt "core::marker::PhantomData" 0 [].

Definition u64_limit : Z := (2 ^ 64)%Z.

Definition usize_limit : Z := (2 ^ 64)%Z.

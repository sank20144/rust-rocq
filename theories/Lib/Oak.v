From RustRocq Require Import Syntax LayoutAlg Memory Denote.
From RustRocq Require Import Lib.Models Lib.X86_64 Lib.Core Lib.Bitvec Lib.Iter Lib.Fmt.
From Stdlib Require Import String List.
Import ListNotations.

Section Oracle.

Context `{Alg : LayoutAlg}.

Definition oak_first_order (overflow_checks : bool) : model :=
  models [x86_64_model; bitvec_model; core_model overflow_checks; iter_constructors; fmt_model].

Definition oak_oracle (overflow_checks : bool) : oracle :=
  fun cb adts f targs vs st =>
    match iter_model adts f targs vs with
    | Some m => hresult (m cb) st
    | None => Some (oak_first_order overflow_checks adts f targs vs st)
    end.

Lemma oak_oracle_monotone overflow_checks : oracle_monotone (oak_oracle overflow_checks).
Proof.
  intros c1 c2 Hle adts f targs vs st o H. unfold oak_oracle in *.
  destruct (iter_model adts f targs vs) as [m|] eqn:E; [|exact H].
  exact (hresult_mono m (iter_model_mono adts f targs vs m E) c1 c2 Hle st o H).
Qed.

End Oracle.

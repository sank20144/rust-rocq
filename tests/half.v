From RustRocq Require Import Syntax Memory Denote.
From Generated Require Import half.
From Stdlib Require Import String List ZArith Lia.
Import ListNotations.

Local Open Scope Z_scope.

Definition P : program := only_adts [].

Definition answer_matches (a e : answer) : bool :=
  match a, e with
  | ARet (VBits W8 z), ARet (VBits W8 z') => Z.eqb z z'
  | APanic, APanic => true
  | _, _ => false
  end.

Lemma answer_matches_eq : forall a e, answer_matches a e = true -> a = e.
Proof.
  intros a e H.
  destruct a as [v| | | | |]; try (destruct v as [| | |w z| | | |]; try destruct w);
    destruct e as [v'| | | | |]; try (destruct v' as [| | |w' z'| | | |]; try destruct w');
    cbn in H; try discriminate; try reflexivity.
  apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Definition runs_to (b : body) (args : list runtime_value) (e : answer) : bool :=
  match option_map answer_of (run_with P b [] args 40%nat) with
  | Some a => answer_matches a e
  | None => false
  end.

Lemma runs_to_means : forall b args e, runs_to b args e = true -> Means P b [] args e.
Proof.
  unfold runs_to. intros b args e H.
  destruct (option_map answer_of (run_with P b [] args 40%nat)) as [a|] eqn:E; [|discriminate].
  apply answer_matches_eq in H. subst.
  exact (means_within P 40%nat b [] args _ E).
Qed.

Definition every_u8 (p : Z -> bool) : bool :=
  forallb (fun x => p (Z.of_nat x)) (seq 0 256).

Lemma every_u8_spec : forall p, every_u8 p = true -> forall x, 0 <= x < 256 -> p x = true.
Proof.
  unfold every_u8. intros p H x Hx.
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma half_up_on_every_u8 :
  every_u8 (fun x => runs_to half_up [VBits W8 x] (ARet (VBits W8 ((x + 1) / 2)))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma naive_half_up_on_every_u8 :
  every_u8 (fun x => runs_to naive_half_up [VBits W8 x]
    (if x =? 255 then APanic else ARet (VBits W8 ((x + 1) / 2)))) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem half_up_never_panics :
  forall x, 0 <= x < 256 ->
  Means P half_up [] [VBits W8 x] (ARet (VBits W8 ((x + 1) / 2))).
Proof.
  intros x Hx. apply runs_to_means.
  exact (every_u8_spec _ half_up_on_every_u8 x Hx).
Qed.

Theorem naive_half_up_panics_only_on_255 :
  forall x, 0 <= x < 256 ->
  Means P naive_half_up [] [VBits W8 x]
    (if x =? 255 then APanic else ARet (VBits W8 ((x + 1) / 2))).
Proof.
  intros x Hx. apply runs_to_means.
  exact (every_u8_spec _ naive_half_up_on_every_u8 x Hx).
Qed.

Theorem the_two_agree_below_255 :
  forall x a, 0 <= x < 255 ->
  Means P naive_half_up [] [VBits W8 x] a -> Means P half_up [] [VBits W8 x] a.
Proof.
  intros x a Hx H.
  pose proof (naive_half_up_panics_only_on_255 x ltac:(lia)) as H'.
  replace (x =? 255) with false in H' by (symmetry; apply Z.eqb_neq; lia).
  rewrite (means_deterministic _ _ _ _ _ _ H H').
  apply half_up_never_panics. lia.
Qed.

From RustRocq Require Import Syntax Memory.
From Stdlib Require Import Bool List ZArith Lia.
Import ListNotations.

Section Ranges.

  Lemma length_splice : forall offset (part whole : list mbyte),
    offset + length part <= length whole -> length (splice offset part whole) = length whole.
  Proof.
    intros offset part whole H. unfold splice.
    rewrite !length_app, length_firstn, length_skipn. lia.
  Qed.

  Lemma nth_error_splice : forall offset (part whole : list mbyte) k,
    offset + length part <= length whole ->
    nth_error (splice offset part whole) k =
      if k <? offset then nth_error whole k
      else if k <? offset + length part then nth_error part (k - offset)
      else nth_error whole k.
  Proof.
    intros offset part whole k H. unfold splice.
    destruct (Nat.ltb_spec k offset).
    - rewrite nth_error_app1 by (rewrite length_firstn; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec k offset); [reflexivity | lia].
    - rewrite nth_error_app2 by (rewrite length_firstn; lia).
      rewrite length_firstn, Nat.min_l by lia.
      destruct (Nat.ltb_spec k (offset + length part)).
      + rewrite nth_error_app1 by lia. reflexivity.
      + rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
  Qed.

  Lemma length_bytes_at : forall offset size (bs : list mbyte),
    offset + size <= length bs -> length (bytes_at offset size bs) = size.
  Proof.
    intros offset size bs H. unfold bytes_at. rewrite length_firstn, length_skipn. lia.
  Qed.

  Lemma nth_error_bytes_at : forall offset size (bs : list mbyte) k,
    nth_error (bytes_at offset size bs) k =
      if k <? size then nth_error bs (offset + k) else None.
  Proof.
    intros offset size bs k. unfold bytes_at.
    rewrite nth_error_firstn, nth_error_skipn. reflexivity.
  Qed.

  Lemma bytes_at_splice_same : forall offset (part whole : list mbyte),
    offset + length part <= length whole ->
    bytes_at offset (length part) (splice offset part whole) = part.
  Proof.
    intros offset part whole H. apply nth_error_ext. intros k.
    rewrite nth_error_bytes_at, nth_error_splice by exact H.
    destruct (Nat.ltb_spec k (length part)).
    - destruct (Nat.ltb_spec (offset + k) offset); [lia|].
      destruct (Nat.ltb_spec (offset + k) (offset + length part)); [|lia].
      f_equal. lia.
    - symmetry. apply nth_error_None. lia.
  Qed.

  Lemma bytes_at_splice_apart : forall offset size offset' (part whole : list mbyte),
    offset' + length part <= length whole ->
    offset + size <= offset' \/ offset' + length part <= offset ->
    bytes_at offset size (splice offset' part whole) = bytes_at offset size whole.
  Proof.
    intros offset size offset' part whole H Hd. apply nth_error_ext. intros k.
    rewrite !nth_error_bytes_at.
    destruct (Nat.ltb_spec k size); [|reflexivity].
    rewrite nth_error_splice by exact H.
    destruct (Nat.ltb_spec (offset + k) offset'); [reflexivity|].
    destruct (Nat.ltb_spec (offset + k) (offset' + length part)); [lia | reflexivity].
  Qed.

  Lemma splice_splice_same : forall offset (part part' whole : list mbyte),
    length part = length part' -> offset + length part <= length whole ->
    splice offset part' (splice offset part whole) = splice offset part' whole.
  Proof.
    intros offset part part' whole Hl H. apply nth_error_ext. intros k.
    rewrite !nth_error_splice by (rewrite ?length_splice; lia).
    repeat match goal with |- context [?a <? ?b] => destruct (Nat.ltb_spec a b) end;
      reflexivity || lia.
  Qed.

  Lemma splice_comm : forall o1 o2 (b1 b2 whole : list mbyte),
    o1 + length b1 <= length whole -> o2 + length b2 <= length whole ->
    o1 + length b1 <= o2 \/ o2 + length b2 <= o1 ->
    splice o1 b1 (splice o2 b2 whole) = splice o2 b2 (splice o1 b1 whole).
  Proof.
    intros o1 o2 b1 b2 whole H1 H2 Hd. apply nth_error_ext. intros k.
    rewrite !nth_error_splice by (rewrite ?length_splice; lia).
    repeat match goal with |- context [?a <? ?b] => destruct (Nat.ltb_spec a b) end;
      reflexivity || lia.
  Qed.

  Lemma bytes_at_bytes_at : forall offset size offset' size' (bs : list mbyte),
    offset + size <= size' ->
    bytes_at offset size (bytes_at offset' size' bs) = bytes_at (offset' + offset) size bs.
  Proof.
    intros offset size offset' size' bs H. apply nth_error_ext. intros k.
    rewrite !nth_error_bytes_at.
    destruct (Nat.ltb_spec k size); [|reflexivity].
    destruct (Nat.ltb_spec (offset + k) size'); [|lia].
    f_equal. lia.
  Qed.

  Lemma splice_inside : forall offset part offset' size' (whole : list mbyte),
    offset' + size' <= length whole -> offset + length part <= size' ->
    splice offset' (splice offset part (bytes_at offset' size' whole)) whole
    = splice (offset' + offset) part whole.
  Proof.
    intros offset part offset' size' whole H Hp. apply nth_error_ext. intros k.
    assert (Hs : length (bytes_at offset' size' whole) = size') by (apply length_bytes_at; lia).
    rewrite !nth_error_splice by (rewrite ?length_splice; lia).
    rewrite !nth_error_bytes_at, length_splice, Hs by lia.
    repeat match goal with |- context [?a <? ?b] => destruct (Nat.ltb_spec a b) end;
      try reflexivity; try lia; f_equal; lia.
  Qed.

  Lemma splice_whole : forall (part whole : list mbyte),
    length part = length whole -> splice 0 part whole = part.
  Proof.
    intros part whole H. unfold splice. simpl. rewrite H, skipn_all, app_nil_r. reflexivity.
  Qed.

  Lemma bytes_at_whole : forall (bs : list mbyte), bytes_at 0 (length bs) bs = bs.
  Proof. intros bs. unfold bytes_at. simpl. apply firstn_all. Qed.

End Ranges.

Section LittleEndian.

  Lemma length_little_endian : forall n z, length (little_endian n z) = n.
  Proof. induction n as [|n IH]; intros z; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma length_int_bytes : forall n z p, length (int_bytes n z p) = n.
  Proof. intros n z p. unfold int_bytes. rewrite length_map. apply length_little_endian. Qed.

  Lemma from_little_endian_bytes : forall n z,
    from_little_endian (little_endian n z) = (z mod 256 ^ Z.of_nat n)%Z.
  Proof.
    induction n as [|n IH]; intros z; simpl little_endian; simpl from_little_endian.
    - rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
    - rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Z.rem_mul_r by lia. reflexivity.
  Qed.

  Lemma byte_values_int_bytes : forall n z p,
    byte_values (int_bytes n z p) = Some (little_endian n z).
  Proof.
    intros n z p. unfold int_bytes. induction (little_endian n z) as [|b bs IH]; simpl;
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  Lemma int_value_int_bytes : forall n z p,
    (0 <= z < 256 ^ Z.of_nat n)%Z -> int_value (int_bytes n z p) = AccessOk z.
  Proof.
    intros n z p H. unfold int_value. rewrite byte_values_int_bytes, from_little_endian_bytes.
    rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Lemma width_limit_bytes : forall w, width_limit w = (256 ^ Z.of_nat (int_width_bytes w))%Z.
  Proof. intros w. destruct w; reflexivity. Qed.

  Lemma word_range_bytes : (2 ^ 64 = 256 ^ Z.of_nat pointer_bytes)%Z.
  Proof. reflexivity. Qed.

End LittleEndian.

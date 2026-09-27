From RustRocq Require Import Syntax LayoutAlg Memory Proof.Bytes.
From Stdlib Require Import Bool List ZArith Lia.
Import ListNotations.

Local Open Scope list_scope.

Section Induction.

  Variable P : layout -> Prop.

  Hypothesis case_int : forall w, P (LInt w).
  Hypothesis case_bool : P LBool.
  Hypothesis case_char : P LChar.
  Hypothesis case_raw : forall k, P (LRawPtr k).
  Hypothesis case_ref : forall t k, P (LRef t k).
  Hypothesis case_unit : P LUnit.
  Hypothesis case_never : P LNever.
  Hypothesis case_array : forall e n, P e -> P (LArray e n).
  Hypothesis case_struct : forall d size align fields,
    Forall (fun f => P (snd f)) fields -> P (LStruct d size align fields).
  Hypothesis case_enum : forall d size align tag_offset tag_size variants,
    Forall P variants -> P (LEnum d size align tag_offset tag_size variants).

  Fixpoint layout_induction (l : layout) : P l :=
    match l with
    | LInt w => case_int w
    | LBool => case_bool
    | LChar => case_char
    | LRawPtr k => case_raw k
    | LRef t k => case_ref t k
    | LUnit => case_unit
    | LNever => case_never
    | LArray e n => case_array e n (layout_induction e)
    | LStruct d size align fields =>
        case_struct d size align fields
          ((fix go (fs : list (nat * layout)) : Forall (fun f => P (snd f)) fs :=
              match fs with
              | [] => Forall_nil _
              | (o, f) :: rest => Forall_cons (o, f) (layout_induction f) (go rest)
              end) fields)
    | LEnum d size align tag_offset tag_size variants =>
        case_enum d size align tag_offset tag_size variants
          ((fix go (vs : list layout) : Forall P vs :=
              match vs with
              | [] => Forall_nil _
              | v :: rest => Forall_cons v (layout_induction v) (go rest)
              end) variants)
    end.

End Induction.

Section WellFormed.

  Definition ranges (fields : list (nat * layout)) : list (nat * nat) :=
    map (fun f => (fst f, size_of (snd f))) fields.

  Definition struct_ok (size align : nat) (fields : list (nat * layout)) : Prop :=
    1 <= align /\ Nat.divide align size /\ (Z.of_nat size <= max_isize)%Z
    /\ Forall (fun f => fst f + size_of (snd f) <= size /\ Nat.divide (align_of (snd f)) (fst f)
                        /\ Nat.divide (align_of (snd f)) align) fields
    /\ pairwise_apart (ranges fields).

  Definition enum_ok (size align tag_offset tag_size : nat) (variants : list layout) : Prop :=
    1 <= align /\ Nat.divide align size /\ (Z.of_nat size <= max_isize)%Z
    /\ tag_offset + tag_size <= size
    /\ (Z.of_nat (length variants) <= 256 ^ Z.of_nat tag_size)%Z
    /\ Forall (fun v => exists fields, v = LStruct None size align fields
                        /\ struct_ok size align fields
                        /\ Forall (fun r => apart tag_offset tag_size (fst r) (snd r))
                                  (ranges fields)) variants.

  Fixpoint layout_wf (l : layout) : Prop :=
    match l with
    | LArray e _ => layout_wf e
    | LStruct _ size align fields =>
        struct_ok size align fields
        /\ fold_right and True (map (fun '(_, f) => layout_wf f) fields)
    | LEnum _ size align tag_offset tag_size variants =>
        enum_ok size align tag_offset tag_size variants
        /\ fold_right and True (map layout_wf variants)
    | _ => True
    end.

  Lemma fields_wf_iff : forall (fields : list (nat * layout)),
    fold_right and True (map (fun '(_, f) => layout_wf f) fields)
    <-> Forall (fun f => layout_wf (snd f)) fields.
  Proof.
    induction fields as [|[o f] fields IH]; simpl; split; intros H; auto.
    - destruct H as [Hf Hrest]. constructor; [exact Hf | apply IH; exact Hrest].
    - inversion H; subst. split; [assumption | apply IH; assumption].
  Qed.

  Lemma variants_wf_iff : forall (variants : list layout),
    fold_right and True (map layout_wf variants) <-> Forall layout_wf variants.
  Proof.
    induction variants as [|v variants IH]; simpl; split; intros H; auto.
    - destruct H as [Hv Hrest]. constructor; [exact Hv | apply IH; exact Hrest].
    - inversion H; subst. split; [assumption | apply IH; assumption].
  Qed.

  Lemma struct_fields_wf : forall d size align fields,
    layout_wf (LStruct d size align fields) -> Forall (fun f => layout_wf (snd f)) fields.
  Proof. intros d size align fields [_ H]. apply fields_wf_iff. exact H. Qed.

  Lemma enum_variants_wf : forall d size align tag_offset tag_size variants,
    layout_wf (LEnum d size align tag_offset tag_size variants) -> Forall layout_wf variants.
  Proof. intros d size align tag_offset tag_size variants [_ H]. apply variants_wf_iff. exact H. Qed.

  Lemma struct_wf_intro : forall d size align fields,
    struct_ok size align fields -> Forall (fun f => layout_wf (snd f)) fields ->
    layout_wf (LStruct d size align fields).
  Proof. intros d size align fields Hok H. split; [exact Hok | apply fields_wf_iff; exact H]. Qed.

  Lemma enum_wf_intro : forall d size align tag_offset tag_size variants,
    enum_ok size align tag_offset tag_size variants -> Forall layout_wf variants ->
    layout_wf (LEnum d size align tag_offset tag_size variants).
  Proof.
    intros d size align tag_offset tag_size variants Hok H.
    split; [exact Hok | apply variants_wf_iff; exact H].
  Qed.

  Definition basic (l : layout) : Prop := 1 <= align_of l /\ Nat.divide (align_of l) (size_of l).

  Lemma wf_basic : forall l, layout_wf l -> basic l.
  Proof.
    apply (layout_induction (fun l => layout_wf l -> basic l)); intros; unfold basic; simpl.
    - destruct w; simpl; split; try lia; apply Nat.divide_refl.
    - split; [lia | apply Nat.divide_refl].
    - split; [lia | apply Nat.divide_refl].
    - split; [unfold pointer_bytes; lia|]. destruct k; simpl.
      + apply Nat.divide_refl.
      + exists 2. reflexivity.
      + exists 2. reflexivity.
    - split; [unfold pointer_bytes; lia|]. destruct k; simpl.
      + apply Nat.divide_refl.
      + exists 2. reflexivity.
      + exists 2. reflexivity.
    - split; [lia | apply Nat.divide_0_r].
    - split; [lia | apply Nat.divide_0_r].
    - destruct (H H0) as [Ha Hd]. split; [exact Ha|].
      apply Nat.divide_mul_r. exact Hd.
    - destruct H0 as [[Ha [Hd _]] _]. split; assumption.
    - destruct H0 as [[Ha [Hd _]] _]. split; assumption.
  Qed.

End WellFormed.

Section LayoutOfWellFormed.

  Context `{Alg : LayoutAlg}.

  Lemma divide_of_aligned : forall a o, 1 <= a -> aligned a o -> Nat.divide a o.
  Proof. intros a o Ha H. apply Nat.Lcm0.mod_divide. exact H. Qed.

  Lemma ranges_combine : forall (offs : list nat) (fields : list layout),
    ranges (combine offs fields) = combine offs (map size_of fields).
  Proof.
    induction offs as [|o offs IH]; intros [|f fields]; simpl; try reflexivity.
    rewrite IH. reflexivity.
  Qed.

  Lemma map_fst_size_align : forall (fields : list layout),
    map fst (map size_align_of fields) = map size_of fields.
  Proof. induction fields as [|f fields IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma combine_fields_ok : forall (fields : list layout) (offs : list nat) size align,
    Forall layout_wf fields ->
    Forall2 (fun f o => fits o (fst f) size /\ aligned (snd f) o) (map size_align_of fields) offs ->
    Forall (fun f => Nat.divide (snd f) align) (map size_align_of fields) ->
    Forall (fun f => fst f + size_of (snd f) <= size /\ Nat.divide (align_of (snd f)) (fst f)
                     /\ Nat.divide (align_of (snd f)) align) (combine offs fields).
  Proof.
    induction fields as [|f fields IH]; intros offs size align Hwf Hp Ha.
    { inversion Hp; subst. constructor. }
    inversion Hp as [|? o ? offs' [Hfit Hal] Hrest]; subst. simpl.
    inversion Hwf as [|? ? Hf Hfs]; subst. inversion Ha as [|? ? Haf Has]; subst.
    destruct (wf_basic f Hf) as [Hb _].
    constructor; [|apply IH; assumption].
    unfold fits in Hfit. simpl in *.
    split; [lia|]. split; [apply divide_of_aligned; assumption | exact Haf].
  Qed.

  Lemma combine_wf : forall (fields : list layout) (offs : list nat),
    Forall layout_wf fields -> Forall (fun f => layout_wf (snd f)) (combine offs fields).
  Proof.
    induction fields as [|f fields IH]; intros [|o offs] H; simpl; try constructor;
      inversion H; subst; [assumption | apply IH; assumption].
  Qed.

  Lemma struct_ok_of_alg : forall n (fields : list layout) r a,
    Forall layout_wf fields -> struct_alg n (map size_align_of fields) r = Some a ->
    struct_ok (ag_size a) (ag_align a) (combine (ag_offsets a) fields).
  Proof.
    intros n fields r a Hwf E.
    destruct (struct_alg_placed n _ r a E) as [_ [Hp Hapart]].
    destruct (struct_alg_wf n _ r a E) as [Ha [Hsz _]].
    pose proof (struct_alg_aligns n _ r a E) as Hal.
    split; [exact Ha|]. split; [apply divide_of_aligned; assumption|].
    split; [destruct (struct_alg_wf n _ r a E) as [_ [_ Hb]]; exact Hb|].
    split; [apply combine_fields_ok; assumption|].
    rewrite ranges_combine, <- map_fst_size_align. exact Hapart.
  Qed.

  Lemma struct_layout_wf : forall declaration n r (fields : list layout) l,
    Forall layout_wf fields -> struct_layout declaration n r fields = Some l -> layout_wf l.
  Proof.
    intros declaration n r fields l Hwf H. unfold struct_layout in H.
    destruct (struct_alg n (map size_align_of fields) r) as [a|] eqn:E; [|discriminate].
    injection H as <-. apply struct_wf_intro; [eapply struct_ok_of_alg; eassumption|].
    apply combine_wf. exact Hwf.
  Qed.

  Lemma apart_combine : forall (fields : list layout) (offs : list nat) tag_offset tag_size,
    Forall (fun r => apart tag_offset tag_size (fst r) (snd r))
           (combine offs (map fst (map size_align_of fields))) ->
    Forall (fun r => apart tag_offset tag_size (fst r) (snd r)) (ranges (combine offs fields)).
  Proof. intros. rewrite ranges_combine, <- map_fst_size_align. assumption. Qed.

  Lemma variant_structs_ok : forall (variants : list (list layout)) (placed : list agg_layout) size align
      tag_offset tag_size,
    Forall (Forall layout_wf) variants ->
    Forall2 (variant_placed tag_offset tag_size size) (map (map size_align_of) variants) placed ->
    1 <= align -> Nat.divide align size -> (Z.of_nat size <= max_isize)%Z ->
    Forall (Forall (fun f => Nat.divide (snd f) align)) (map (map size_align_of) variants) ->
    Forall (fun v => exists fields, v = LStruct None size align fields
                     /\ struct_ok size align fields
                     /\ Forall (fun r => apart tag_offset tag_size (fst r) (snd r)) (ranges fields))
           (map (fun '(p, fields) => LStruct None size align (combine (ag_offsets p) fields))
                (combine placed variants))
    /\ Forall layout_wf
           (map (fun '(p, fields) => LStruct None size align (combine (ag_offsets p) fields))
                (combine placed variants)).
  Proof.
    induction variants as [|fs variants IH];
      intros placed size align tag_offset tag_size Hwf Hp Ha Hd Hbound Hal.
    { inversion Hp; subst. split; constructor. }
    inversion Hp as [|? p ? placed' Hv Hrest]; subst. simpl.
    inversion Hwf as [|? ? Hfs Hwfs]; subst. inversion Hal as [|? ? Halfs Hals]; subst.
    destruct (IH placed' size align tag_offset tag_size Hwfs Hrest Ha Hd Hbound Hals) as [IH1 IH2].
    destruct Hv as [[_ [Hpl Hapart]] [Hsize Htag]].
    assert (Hok : struct_ok size align (combine (ag_offsets p) fs)).
    { split; [exact Ha|]. split; [exact Hd|]. split; [exact Hbound|].
      split; [|rewrite ranges_combine, <- map_fst_size_align; exact Hapart].
      pose proof (combine_fields_ok fs (ag_offsets p) (ag_size p) align Hfs Hpl Halfs) as Hc.
      eapply Forall_impl; [|exact Hc]. intros f [H1 H2]. split; [lia | exact H2]. }
    split; constructor.
    - exists (combine (ag_offsets p) fs). split; [reflexivity|]. split; [exact Hok|].
      apply apart_combine. exact Htag.
    - exact IH1.
    - apply struct_wf_intro; [exact Hok | apply combine_wf; exact Hfs].
    - exact IH2.
  Qed.

  Lemma length_combine_eq : forall (A B : Type) (xs : list A) (ys : list B),
    length xs = length ys -> length (combine xs ys) = length xs.
  Proof. intros A B xs ys H. rewrite length_combine, H, Nat.min_id. reflexivity. Qed.

  Lemma enum_layout_wf : forall declaration r (variants : list (list layout)) l,
    Forall (Forall layout_wf) variants ->
    enum_layout_of declaration r variants = Some l -> layout_wf l.
  Proof.
    intros declaration r variants l Hwf H. unfold enum_layout_of in H.
    destruct (enum_alg declaration (map (map size_align_of) variants) r) as [e|] eqn:E;
      [|discriminate].
    injection H as <-.
    destruct (enum_alg_variants _ _ _ _ E) as [Hlen Hplaced].
    destruct (enum_alg_tag _ _ _ _ E) as [Hfits _].
    destruct (enum_alg_wf _ _ _ _ E) as [Ha [Hal0 Hsz]].
    pose proof (enum_alg_aligns _ _ _ _ E) as Hal.
    pose proof (enum_alg_tag_room _ _ _ _ E) as Hroom.
    rewrite length_map in Hlen, Hroom.
    assert (Hd : Nat.divide (en_align e) (en_size e)) by (apply divide_of_aligned; assumption).
    clear Hal0.
    destruct (variant_structs_ok variants (en_variants e) (en_size e) (en_align e)
                (en_tag_offset e) (scalar_bytes (en_tag e)) Hwf Hplaced Ha Hd Hsz Hal) as [Hv Hw].
    apply enum_wf_intro; [|exact Hw].
    split; [exact Ha|]. split; [exact Hd|]. split; [exact Hsz|].
    split; [unfold fits in Hfits; exact Hfits|].
    split; [|exact Hv].
    rewrite length_map, length_combine_eq by lia.
    rewrite Hlen. rewrite Z.pow_mul_r in Hroom by lia. exact Hroom.
  Qed.

  Lemma all_some_forall2 : forall (A B : Type) (f : A -> option B) xs ys,
    all_some (map f xs) = Some ys -> Forall2 (fun x y => f x = Some y) xs ys.
  Proof.
    intros A B f. induction xs as [|x xs IH]; intros ys H; simpl in H.
    - injection H as <-. constructor.
    - destruct (f x) as [y|] eqn:E; [|discriminate].
      destruct (all_some (map f xs)) as [ys'|] eqn:E'; [|discriminate].
      injection H as <-. constructor; [exact E | apply IH; reflexivity].
  Qed.

  Lemma forall_of_forall2 : forall (A B : Type) (R : A -> B -> Prop) (P : B -> Prop) xs ys,
    Forall2 R xs ys -> (forall x y, R x y -> P y) -> Forall P ys.
  Proof.
    intros A B R P xs ys H Himp. induction H; constructor; [eapply Himp; eassumption | assumption].
  Qed.

  Lemma layout_of_fuel_wf : forall adts fuel t l,
    layout_of_fuel adts fuel t = Some l -> layout_wf l.
  Proof.
    intros adts fuel. induction fuel as [|fuel IH]; intros t l H; [discriminate|].
    assert (Hall : forall ts ls, all_some (map (layout_of_fuel adts fuel) ts) = Some ls ->
                                 Forall layout_wf ls).
    { intros ts ls Hs. eapply forall_of_forall2; [apply all_some_forall2; exact Hs|].
      intros x y Hy. eapply IH. exact Hy. }
    destruct t; cbn [layout_of_fuel] in H; try discriminate; try (injection H as <-; exact I).
    - destruct (find_adt adts path) as [d|]; [|discriminate].
      destruct (ad_kind d), (ad_variants d) as [|v [|v' vs]]; try discriminate.
      + destruct (all_some _) as [fields|] eqn:E; [|discriminate].
        eapply struct_layout_wf; [eapply Hall; exact E | exact H].
      + destruct (all_some (map _ [])) as [variants|] eqn:E; [|discriminate].
        eapply enum_layout_wf; [|exact H].
        simpl in E. injection E as <-. constructor.
      + destruct (all_some (map _ (v :: nil))) as [variants|] eqn:E; [|discriminate].
        eapply enum_layout_wf; [|exact H].
        eapply forall_of_forall2; [apply all_some_forall2; exact E|].
        intros x y Hy. eapply Hall. exact Hy.
      + destruct (all_some (map _ (v :: v' :: vs))) as [variants|] eqn:E; [|discriminate].
        eapply enum_layout_wf; [|exact H].
        eapply forall_of_forall2; [apply all_some_forall2; exact E|].
        intros x y Hy. eapply Hall. exact Hy.
    - destruct (layout_of_fuel adts fuel t) as [le|] eqn:E; [|discriminate].
      destruct (const_nat len); [|discriminate].
      injection H as <-. simpl. eapply IH. exact E.
    - eapply IH. exact H.
    - destruct (closure_upvars args) as [u|]; [|discriminate]. eapply IH. exact H.
    - destruct elems as [|t ts]; [injection H as <-; exact I|].
      destruct (all_some _) as [fields|] eqn:E; [|discriminate].
      eapply struct_layout_wf; [eapply Hall; exact E | exact H].
  Qed.

  Lemma layout_of_wf : forall adts t l, layout_of adts t = Some l -> layout_wf l.
  Proof. unfold layout_of. intros adts t l H. exact (layout_of_fuel_wf adts 64 t l H). Qed.

End LayoutOfWellFormed.

Section Placing.

  Fixpoint splice_all (parts : list (nat * list mbyte)) (bytes : list mbyte) : list mbyte :=
    match parts with
    | [] => bytes
    | (offset, part) :: rest => splice_all rest (splice offset part bytes)
    end.

  Fixpoint field_parts (fields : list (nat * (runtime_value -> option (list mbyte))))
      (vs : list runtime_value) : option (list (nat * list mbyte)) :=
    match fields, vs with
    | [], [] => Some []
    | (offset, encode_field) :: fields, v :: vs =>
        match encode_field v, field_parts fields vs with
        | Some part, Some rest => Some ((offset, part) :: rest)
        | _, _ => None
        end
    | _, _ => None
    end.

  Lemma place_fields_parts : forall fields vs bytes,
    place_fields fields vs bytes = option_map (fun parts => splice_all parts bytes) (field_parts fields vs).
  Proof.
    induction fields as [|[o enc] fields IH]; intros [|v vs] bytes; simpl; try reflexivity.
    destruct (enc v) as [part|]; [|reflexivity].
    rewrite IH. destruct (field_parts fields vs); reflexivity.
  Qed.

  Definition part_ranges (parts : list (nat * list mbyte)) : list (nat * nat) :=
    map (fun p => (fst p, length (snd p))) parts.

  Definition parts_inside (size : nat) (parts : list (nat * list mbyte)) : Prop :=
    Forall (fun p => fst p + length (snd p) <= size) parts.

  Lemma length_splice_all : forall parts bytes,
    parts_inside (length bytes) parts -> length (splice_all parts bytes) = length bytes.
  Proof.
    induction parts as [|[o b] parts IH]; intros bytes H; simpl; [reflexivity|].
    inversion H as [|? ? Hp Hrest]; subst. simpl in Hp.
    rewrite IH; [apply length_splice; exact Hp|].
    rewrite length_splice by exact Hp. exact Hrest.
  Qed.

  Lemma bytes_at_splice_all_apart : forall parts bytes offset size,
    parts_inside (length bytes) parts ->
    Forall (fun r => apart offset size (fst r) (snd r)) (part_ranges parts) ->
    bytes_at offset size (splice_all parts bytes) = bytes_at offset size bytes.
  Proof.
    induction parts as [|[o b] parts IH]; intros bytes offset size Hin Hap; simpl; [reflexivity|].
    inversion Hin as [|? ? Hp Hrest]; subst. inversion Hap as [|? ? Ha Hrest']; subst.
    simpl in Hp, Ha.
    rewrite IH; [| rewrite length_splice by exact Hp; exact Hrest | exact Hrest'].
    apply bytes_at_splice_apart; [exact Hp|]. unfold apart in Ha. lia.
  Qed.

  Lemma bytes_at_splice_all : forall parts bytes offset part,
    parts_inside (length bytes) parts -> pairwise_apart (part_ranges parts) ->
    In (offset, part) parts -> bytes_at offset (length part) (splice_all parts bytes) = part.
  Proof.
    induction parts as [|[o b] parts IH]; intros bytes offset part Hin Hap Hmem; [destruct Hmem|].
    inversion Hin as [|? ? Hp Hrest]; subst. simpl in Hp. destruct Hap as [Hhead Htail].
    simpl. destruct Hmem as [Heq|Hmem].
    - injection Heq as <- <-.
      rewrite bytes_at_splice_all_apart;
        [ apply bytes_at_splice_same; exact Hp
        | rewrite length_splice by exact Hp; exact Hrest
        | ].
      eapply Forall_impl; [|exact Hhead]. intros r Hr. exact Hr.
    - apply IH; [rewrite length_splice by exact Hp; exact Hrest | exact Htail | exact Hmem].
  Qed.

  Lemma splice_all_splice_apart : forall parts bytes offset part,
    parts_inside (length bytes) parts -> offset + length part <= length bytes ->
    Forall (fun r => apart offset (length part) (fst r) (snd r)) (part_ranges parts) ->
    splice_all parts (splice offset part bytes) = splice offset part (splice_all parts bytes).
  Proof.
    induction parts as [|[o b] parts IH]; intros bytes offset part Hin Hle Hap; simpl; [reflexivity|].
    inversion Hin as [|? ? Hp Hrest]; subst. inversion Hap as [|? ? Ha Hrest']; subst.
    simpl in Hp, Ha.
    rewrite splice_comm by (unfold apart in Ha; lia).
    apply IH; [rewrite length_splice by exact Hp; exact Hrest | rewrite length_splice; lia | exact Hrest'].
  Qed.

End Placing.

Section Lengths.

  Inductive encoded_fields : list (nat * layout) -> list runtime_value ->
                             list (nat * list mbyte) -> Prop :=
    | encoded_nil : encoded_fields [] [] []
    | encoded_cons : forall o f v b fields vs parts,
        encode f v = Some b -> encoded_fields fields vs parts ->
        encoded_fields ((o, f) :: fields) (v :: vs) ((o, b) :: parts).

  Lemma field_parts_encoded : forall fields vs parts,
    field_parts (map (fun '(o, f) => (o, encode f)) fields) vs = Some parts ->
    encoded_fields fields vs parts.
  Proof.
    induction fields as [|[o f] fields IH]; intros [|v vs] parts H; simpl in H; try discriminate.
    - injection H as <-. constructor.
    - destruct (encode f v) as [b|] eqn:E; [|discriminate].
      destruct (field_parts _ vs) as [rest|] eqn:E'; [|discriminate].
      injection H as <-. constructor; [exact E | apply IH; exact E'].
  Qed.

  Lemma encoded_field_parts : forall fields vs parts,
    encoded_fields fields vs parts ->
    field_parts (map (fun '(o, f) => (o, encode f)) fields) vs = Some parts.
  Proof.
    intros fields vs parts H. induction H; simpl; [reflexivity|].
    rewrite H, IHencoded_fields. reflexivity.
  Qed.

  Lemma encoded_fields_lengths : forall fields vs parts,
    encoded_fields fields vs parts ->
    length vs = length fields /\ length parts = length fields.
  Proof. intros fields vs parts H. induction H; simpl; lia. Qed.

  Lemma encoded_fields_nth : forall fields vs parts i o f,
    encoded_fields fields vs parts -> nth_error fields i = Some (o, f) ->
    exists v b, nth_error vs i = Some v /\ encode f v = Some b /\ nth_error parts i = Some (o, b).
  Proof.
    intros fields vs parts i o f H. revert i. induction H; intros i Hi; destruct i; simpl in *;
      try discriminate.
    - injection Hi as <- <-. exists v, b. auto.
    - apply IHencoded_fields. exact Hi.
  Qed.

  Lemma encode_length : forall l v bs, layout_wf l -> encode l v = Some bs -> length bs = size_of l.
  Proof.
    intros l. induction l using layout_induction;
      try match goal with IH : Forall _ _ |- _ => rename IH into IHf end;
      intros v bs Hwf H; cbn [encode] in H.
    - destruct v; try discriminate.
      destruct (_ && _ && _); [|discriminate]. injection H as <-. apply length_int_bytes.
    - destruct v; try discriminate. injection H as <-. reflexivity.
    - destruct v; try discriminate. destruct (valid_char value); [|discriminate].
      injection H as <-. apply length_int_bytes.
    - destruct v as [| | | pointer| | |]; try discriminate. unfold encode_pointer in H.
      destruct (in_word_range (pointer_address pointer)); [|discriminate].
      destruct k, (pointer_metadata_of pointer) as [|n|concrete]; try discriminate.
      + injection H as <-. reflexivity.
      + destruct (in_word_range (Z.of_nat n)); [|discriminate].
        injection H as <-. reflexivity.
      + injection H as <-. reflexivity.
    - destruct v as [| | | pointer| | |]; try discriminate. unfold encode_pointer in H.
      destruct (in_word_range (pointer_address pointer)); [|discriminate].
      destruct k, (pointer_metadata_of pointer) as [|n|concrete]; try discriminate.
      + injection H as <-. reflexivity.
      + destruct (in_word_range (Z.of_nat n)); [|discriminate].
        injection H as <-. reflexivity.
      + injection H as <-. reflexivity.
    - destruct (struct_fields None v) as [[|]|]; try discriminate. injection H as <-. reflexivity.
    - discriminate.
    - destruct v; try discriminate.
      destruct (Nat.eqb_spec (length elements) n) as [Hn|]; [|discriminate].
      destruct (all_some (map (encode l) elements)) as [parts|] eqn:E; [|discriminate].
      injection H as <-. simpl in Hwf. subst n.
      apply all_some_forall2 in E. simpl.
      induction E as [|x part xs parts Hx Hrest IHE]; simpl; [reflexivity|].
      rewrite length_app, IHE, (IHl x part Hwf Hx). reflexivity.
    - destruct (struct_fields d v) as [vs|]; [|discriminate].
      rewrite place_fields_parts in H.
      destruct (field_parts _ vs) as [parts|] eqn:E; [|discriminate].
      injection H as <-. apply field_parts_encoded in E.
      pose proof (struct_fields_wf _ _ _ _ Hwf) as Hfw.
      destruct Hwf as [[_ [_ [_ [Hfits _]]]] _].
      rewrite length_splice_all; [apply repeat_length|].
      rewrite repeat_length. clear -E IHf Hfw Hfits.
      induction E as [|o f v b fields vs parts Hb Hrest IHE]; constructor.
      + inversion IHf as [|? ? Hf Hfs]; subst. inversion Hfw as [|? ? Hwf Hwfs]; subst.
        inversion Hfits as [|? ? [Hfit _] _]; subst. simpl in *.
        rewrite (Hf v b Hwf Hb). exact Hfit.
      + inversion IHf; subst. inversion Hfw; subst. inversion Hfits; subst.
        apply IHE; assumption.
    - destruct v as [| | | | | |d' k vs]; try discriminate.
      destruct (String.eqb d d'); [|discriminate].
      rewrite nth_error_map in H.
      destruct (nth_error variants k) as [variant|] eqn:Ev; [|discriminate]. simpl in H.
      destruct (encode variant (VTuple vs)) as [bs'|] eqn:Eb; [|discriminate].
      injection H as <-.
      pose proof (enum_variants_wf _ _ _ _ _ _ Hwf) as Hvw.
      destruct Hwf as [[_ [_ [_ [Htag [_ Hvs]]]]] _].
      assert (Hin : In variant variants) by (eapply nth_error_In; exact Ev).
      rewrite Forall_forall in IHf, Hvw, Hvs.
      destruct (Hvs variant Hin) as [fields [-> _]].
      pose proof (IHf _ Hin (VTuple vs) bs' (Hvw _ Hin) Eb) as Hl. simpl in Hl.
      rewrite length_splice; [exact Hl|]. rewrite length_int_bytes. lia.
  Qed.

End Lengths.

Section Chunks.

  Lemma forall_skipn : forall (A : Type) (P : A -> Prop) n l, Forall P l -> Forall P (skipn n l).
  Proof.
    intros A P n. induction n as [|n IH]; intros [|x l] H; simpl; auto.
    inversion H; subst. apply IH. assumption.
  Qed.

  Lemma skipn_concat : forall (parts : list (list mbyte)) s j,
    Forall (fun p => length p = s) parts -> j <= length parts ->
    skipn (j * s) (concat parts) = concat (skipn j parts).
  Proof.
    induction parts as [|p parts IH]; intros s j Hl Hj; destruct j; simpl in *; try reflexivity.
    - lia.
    - inversion Hl as [|? ? Hp Hrest]; subst.
      rewrite skipn_app, skipn_all2 by lia. simpl.
      replace (length p + j * length p - length p) with (j * length p) by lia.
      apply IH; [exact Hrest | lia].
  Qed.

  Lemma firstn_concat : forall (parts : list (list mbyte)) s c,
    Forall (fun p => length p = s) parts -> c <= length parts ->
    firstn (c * s) (concat parts) = concat (firstn c parts).
  Proof.
    induction parts as [|p parts IH]; intros s c Hl Hc; destruct c; simpl in *; try reflexivity.
    - lia.
    - inversion Hl as [|? ? Hp Hrest]; subst.
      rewrite firstn_app, firstn_all2 by lia.
      replace (length p + c * length p - length p) with (c * length p) by lia.
      rewrite IH; [reflexivity | exact Hrest | lia].
  Qed.

  Lemma bytes_at_concat : forall (parts : list (list mbyte)) s j c,
    Forall (fun p => length p = s) parts -> j + c <= length parts ->
    bytes_at (j * s) (c * s) (concat parts) = concat (firstn c (skipn j parts)).
  Proof.
    intros parts s j c Hl H. unfold bytes_at.
    rewrite skipn_concat by (assumption || lia).
    apply firstn_concat; [apply forall_skipn; exact Hl | rewrite length_skipn; lia].
  Qed.

  Lemma length_concat_uniform : forall (parts : list (list mbyte)) s,
    Forall (fun p => length p = s) parts -> length (concat parts) = length parts * s.
  Proof.
    induction parts as [|p parts IH]; intros s H; simpl; [reflexivity|].
    inversion H; subst. rewrite length_app, (IH (length p)); [lia | assumption].
  Qed.

  Lemma chunks_concat : forall (parts : list (list mbyte)) s,
    Forall (fun p => length p = s) parts -> chunks s (length parts) (concat parts) = parts.
  Proof.
    intros parts s H. apply nth_error_ext. intros i. unfold chunks.
    rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec i (length parts)) as [Hi|Hi]; simpl.
    - pose proof (bytes_at_concat parts s i 1 H ltac:(lia)) as E.
      replace (1 * s) with s in E by lia. rewrite E.
      destruct (nth_error parts i) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
      rewrite <- (firstn_skipn i parts) in Ep. rewrite nth_error_app2 in Ep
        by (rewrite length_firstn; lia).
      rewrite length_firstn, Nat.min_l, Nat.sub_diag in Ep by lia.
      destruct (skipn i parts) as [|q rest]; [discriminate|]. simpl in Ep. injection Ep as ->.
      simpl. rewrite app_nil_r. reflexivity.
    - symmetry. apply nth_error_None. exact Hi.
  Qed.

End Chunks.

Section Paths.

  Inductive step := Field (i : nat) | Elements (first count : nat).

  Definition field_at (l : layout) (v : runtime_value) (i : nat)
      : option (nat * layout * runtime_value) :=
    let pick fields vs :=
      match nth_error fields i, nth_error vs i with
      | Some (o, f), Some x => Some (o, f, x)
      | _, _ => None
      end in
    match l with
    | LStruct d _ _ fields =>
        match struct_fields d v with
        | Some vs => pick fields vs
        | None => None
        end
    | LEnum d _ _ _ _ variants =>
        match v with
        | VAdt d' k vs =>
            if String.eqb d d' then
              match nth_error variants k with
              | Some (LStruct None _ _ fields) => pick fields vs
              | _ => None
              end
            else None
        | _ => None
        end
    | _ => None
    end.

  Definition elements_at (l : layout) (v : runtime_value) (first count : nat)
      : option (nat * layout * runtime_value) :=
    match l, v with
    | LArray e n, VArray vs =>
        if first + count <=? n
        then Some (first * size_of e, LArray e count, VArray (firstn count (skipn first vs)))
        else None
    | _, _ => None
    end.

  Definition step_at (l : layout) (v : runtime_value) (s : step)
      : option (nat * layout * runtime_value) :=
    match s with
    | Field i => field_at l v i
    | Elements first count => elements_at l v first count
    end.

  Fixpoint at_path (l : layout) (v : runtime_value) (p : list step)
      : option (nat * layout * runtime_value) :=
    match p with
    | [] => Some (0, l, v)
    | s :: rest =>
        match step_at l v s with
        | Some (o, l', v') =>
            match at_path l' v' rest with
            | Some (o', l'', v'') => Some (o + o', l'', v'')
            | None => None
            end
        | None => None
        end
    end.

  Fixpoint vtable_free (v : runtime_value) : bool :=
    match v with
    | VPtr p =>
        match pointer_provenance_of p, pointer_metadata_of p with
        | ProvenanceVTable _, _ | _, PointerVTable _ => false
        | _, _ => true
        end
    | VArray vs | VTuple vs | VAdt _ _ vs => forallb vtable_free vs
    | _ => true
    end.

End Paths.

Section Extraction.

  Lemma encoded_ranges : forall fields vs parts,
    encoded_fields fields vs parts -> Forall (fun f => layout_wf (snd f)) fields ->
    part_ranges parts = ranges fields.
  Proof.
    intros fields vs parts H Hwf. induction H; simpl; [reflexivity|].
    inversion Hwf as [|? ? Hf Hrest]; subst. simpl in Hf.
    rewrite (encode_length f v b Hf H), IHencoded_fields by exact Hrest. reflexivity.
  Qed.

  Lemma encoded_inside : forall fields vs parts size,
    encoded_fields fields vs parts -> Forall (fun f => layout_wf (snd f)) fields ->
    Forall (fun f => fst f + size_of (snd f) <= size) fields -> parts_inside size parts.
  Proof.
    intros fields vs parts size H Hwf Hfit. induction H; constructor;
      inversion Hwf as [|? ? Hf Hrest]; subst; inversion Hfit as [|? ? Hfi Hfits]; subst;
      simpl in *.
    - rewrite (encode_length f v b Hf H). exact Hfi.
    - apply IHencoded_fields; assumption.
  Qed.

  Lemma struct_field_encode : forall d size align fields v bs vs i o f x,
    layout_wf (LStruct d size align fields) -> encode (LStruct d size align fields) v = Some bs ->
    struct_fields d v = Some vs -> nth_error fields i = Some (o, f) -> nth_error vs i = Some x ->
    layout_wf f /\ o + size_of f <= size /\ Nat.divide (align_of f) align
    /\ Nat.divide (align_of f) o /\ encode f x = Some (bytes_at o (size_of f) bs).
  Proof.
    intros d size align fields v bs vs i o f x Hwf H Hvs Hf Hx.
    pose proof (struct_fields_wf _ _ _ _ Hwf) as Hfw.
    destruct Hwf as [[_ [_ [_ [Hfits Hapart]]]] _].
    simpl in H. rewrite Hvs, place_fields_parts in H.
    destruct (field_parts _ vs) as [parts|] eqn:E; [|discriminate].
    injection H as <-. apply field_parts_encoded in E.
    assert (Hin : In (o, f) fields) by (eapply nth_error_In; exact Hf).
    rewrite Forall_forall in Hfw, Hfits.
    pose proof (Hfw _ Hin) as Hwff. destruct (Hfits _ Hin) as [Hfit [Hdo Hda]]. simpl in *.
    split; [exact Hwff|]. split; [exact Hfit|]. split; [exact Hda|]. split; [exact Hdo|].
    destruct (encoded_fields_nth fields vs parts i o f E Hf) as [x' [b [Hx' [Hb Hp]]]].
    rewrite Hx in Hx'. injection Hx' as <-. rewrite Hb. f_equal.
    rewrite <- (encode_length f x b Hwff Hb). symmetry.
    apply bytes_at_splice_all.
    - rewrite repeat_length. eapply encoded_inside; [exact E | |].
      + apply Forall_forall. exact Hfw.
      + apply Forall_forall. intros g Hg. apply Hfits. exact Hg.
    - rewrite (encoded_ranges fields vs parts E); [exact Hapart|]. apply Forall_forall. exact Hfw.
    - eapply nth_error_In. exact Hp.
  Qed.

  Lemma variant_of_enum : forall d size align tag_offset tag_size variants k variant,
    layout_wf (LEnum d size align tag_offset tag_size variants) ->
    nth_error variants k = Some variant ->
    exists fields, variant = LStruct None size align fields
      /\ layout_wf variant
      /\ Forall (fun r => apart tag_offset tag_size (fst r) (snd r)) (ranges fields).
  Proof.
    intros d size align tag_offset tag_size variants k variant Hwf Hk.
    pose proof (enum_variants_wf _ _ _ _ _ _ Hwf) as Hvw.
    destruct Hwf as [[_ [_ [_ [_ [_ Hvs]]]]] _].
    assert (Hin : In variant variants) by (eapply nth_error_In; exact Hk).
    rewrite Forall_forall in Hvw, Hvs.
    destruct (Hvs _ Hin) as [fields [-> [_ Hap]]].
    exists fields. split; [reflexivity|]. split; [apply Hvw; exact Hin | exact Hap].
  Qed.

  Lemma all_some_firstn_skipn : forall (A B : Type) (g : A -> option B) xs ys j c,
    all_some (map g xs) = Some ys ->
    all_some (map g (firstn c (skipn j xs))) = Some (firstn c (skipn j ys)).
  Proof.
    intros A B g xs ys j c H. apply all_some_forall2 in H.
    assert (H' : Forall2 (fun x y => g x = Some y) (firstn c (skipn j xs)) (firstn c (skipn j ys))).
    { revert j c. induction H as [|x y xs ys Hxy Hrest IH]; intros j c.
      - rewrite !skipn_nil, !firstn_nil. constructor.
      - destruct j as [|j]; [destruct c as [|c]; simpl; [constructor|]|simpl; apply IH].
        constructor; [exact Hxy|]. rewrite <- (skipn_O xs), <- (skipn_O ys). apply IH. }
    clear H. induction H' as [|x y xs' ys' Hxy Hrest IH]; simpl; [reflexivity|].
    rewrite Hxy, IH. reflexivity.
  Qed.

  Lemma step_encode : forall l v s o l' v' bs,
    layout_wf l -> encode l v = Some bs -> step_at l v s = Some (o, l', v') ->
    layout_wf l' /\ o + size_of l' <= size_of l /\ Nat.divide (align_of l') (align_of l)
    /\ Nat.divide (align_of l') o /\ encode l' v' = Some (bytes_at o (size_of l') bs).
  Proof.
    intros l v [i|first count] o l' v' bs Hwf H Hs; simpl in Hs.
    - unfold field_at in Hs. destruct l; try discriminate.
      + destruct (struct_fields declaration v) as [vs|] eqn:Hvs; [|discriminate].
        destruct (nth_error fields i) as [[o0 f]|] eqn:Hf; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-.
        eapply struct_field_encode; eassumption.
      + destruct v as [| | | | | |d' k vs]; try discriminate.
        destruct (String.eqb_spec declaration d') as [<-|]; [|discriminate].
        destruct (nth_error variants k) as [variant|] eqn:Hk; [|discriminate].
        destruct (variant_of_enum _ _ _ _ _ _ _ _ Hwf Hk) as [fields [-> [Hvwf Hap]]].
        destruct (nth_error fields i) as [[o0 f]|] eqn:Hf; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-.
        cbn [encode] in H. rewrite String.eqb_refl, nth_error_map, Hk in H. cbn [option_map] in H.
        destruct (encode (LStruct None size align fields) (VTuple vs)) as [vb|] eqn:Hvb;
          [|discriminate].
        injection H as <-.
        destruct (struct_field_encode None size align fields (VTuple vs) vb vs i o0 f x
                    Hvwf Hvb eq_refl Hf Hx) as [Hwff [Hfit [Hda [Hdo Henc]]]].
        split; [exact Hwff|]. split; [exact Hfit|]. split; [exact Hda|]. split; [exact Hdo|].
        rewrite Henc. f_equal. symmetry. apply bytes_at_splice_apart.
        * rewrite length_int_bytes, (encode_length _ _ _ Hvwf Hvb). simpl.
          destruct Hwf as [[_ [_ [_ [Htag _]]]] _]. exact Htag.
        * rewrite length_int_bytes.
          assert (Hin : In (o0, size_of f) (ranges fields)).
          { unfold ranges. apply in_map_iff. exists (o0, f). split; [reflexivity|].
            eapply nth_error_In. exact Hf. }
          rewrite Forall_forall in Hap. specialize (Hap _ Hin). unfold apart in Hap. simpl in Hap.
          lia.
    - unfold elements_at in Hs. destruct l; try discriminate. destruct v; try discriminate.
      destruct (Nat.leb_spec (first + count) count0) as [Hle|]; [|discriminate].
      injection Hs as <- <- <-. cbn [encode] in H.
      destruct (Nat.eqb_spec (length elements) count0) as [Hn|]; [|discriminate].
      destruct (all_some (map (encode l) elements)) as [parts|] eqn:E; [|discriminate].
      injection H as <-. cbn [layout_wf] in Hwf.
      pose proof (all_some_forall2 _ _ _ _ _ E) as E2.
      assert (Hlens : Forall (fun p => length p = size_of l) parts).
      { eapply forall_of_forall2; [exact E2|]. intros x y Hy. exact (encode_length l x y Hwf Hy). }
      assert (Hlp : length parts = count0) by (rewrite <- Hn; symmetry; eapply Forall2_length; exact E2).
      destruct (wf_basic l Hwf) as [Ha Hd].
      split; [exact Hwf|]. simpl. split; [nia|]. split; [apply Nat.divide_refl|].
      split; [apply Nat.divide_mul_r; exact Hd|].
      rewrite length_firstn, length_skipn, Nat.min_l by lia.
      rewrite Nat.eqb_refl. rewrite (all_some_firstn_skipn _ _ _ _ _ first count E). simpl.
      f_equal. symmetry. apply bytes_at_concat; [exact Hlens | lia].
  Qed.

  Lemma at_path_encode : forall p l v o l' v' bs,
    layout_wf l -> encode l v = Some bs -> at_path l v p = Some (o, l', v') ->
    layout_wf l' /\ o + size_of l' <= size_of l /\ Nat.divide (align_of l') (align_of l)
    /\ Nat.divide (align_of l') o /\ encode l' v' = Some (bytes_at o (size_of l') bs).
  Proof.
    induction p as [|s p IH]; intros l v o l' v' bs Hwf H Hp; simpl in Hp.
    - injection Hp as <- <- <-. rewrite H. split; [exact Hwf|]. split; [lia|].
      split; [apply Nat.divide_refl|]. split; [apply Nat.divide_0_r|].
      f_equal. rewrite <- (encode_length l v bs Hwf H). symmetry. apply bytes_at_whole.
    - destruct (step_at l v s) as [[[o1 l1] v1]|] eqn:Hs; [|discriminate].
      destruct (at_path l1 v1 p) as [[[o2 l2] v2]|] eqn:Hp2; [|discriminate].
      injection Hp as <- <- <-.
      destruct (step_encode l v s o1 l1 v1 bs Hwf H Hs) as [Hwf1 [Hfit1 [Hda1 [Hdo1 H1]]]].
      destruct (IH l1 v1 o2 l2 v2 _ Hwf1 H1 Hp2) as [Hwf2 [Hfit2 [Hda2 [Hdo2 H2]]]].
      split; [exact Hwf2|]. split; [lia|].
      split; [exact (Nat.divide_trans _ _ _ Hda2 Hda1)|].
      split; [apply Nat.divide_add_r; [exact (Nat.divide_trans _ _ _ Hda2 Hdo1) | exact Hdo2]|].
      rewrite H2, bytes_at_bytes_at by lia. reflexivity.
  Qed.

End Extraction.

Section RoundTrip.

  Lemma all_ok_nth : forall (A B : Type) (g : A -> access_result B) xs ys,
    length xs = length ys ->
    (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> g x = AccessOk y) ->
    all_ok (map g xs) = AccessOk ys.
  Proof.
    intros A B g. induction xs as [|x xs IH]; intros [|y ys] Hl H; simpl in *; try discriminate;
      [reflexivity|].
    rewrite (H 0 x y eq_refl eq_refl). simpl.
    rewrite (IH ys); [reflexivity | lia |].
    intros i x' y' Hx Hy. exact (H (S i) x' y' Hx Hy).
  Qed.

  Lemma struct_fields_shape : forall d v vs, struct_fields d v = Some vs ->
    match d with None => v = VTuple vs | Some p => v = VAdt p 0 vs end.
  Proof.
    intros [p|] [| | | | |fs|p' k fs] vs H; simpl in H; try discriminate.
    - destruct k; [|discriminate]. destruct (String.eqb_spec p p') as [<-|]; [|discriminate].
      injection H as <-. reflexivity.
    - injection H as <-. reflexivity.
  Qed.

  Lemma bytes_at_splice_length : forall offset size part whole,
    length part = size -> offset + size <= length whole ->
    bytes_at offset size (splice offset part whole) = part.
  Proof. intros offset size part whole <- H. apply bytes_at_splice_same. exact H. Qed.

  Lemma forall2_nth_left : forall (A B : Type) (R : A -> B -> Prop) xs ys i x,
    Forall2 R xs ys -> nth_error xs i = Some x -> exists y, nth_error ys i = Some y /\ R x y.
  Proof.
    intros A B R xs ys i x H. revert i. induction H as [|x' y' xs ys Hxy Hrest IH]; intros i Hi;
      destruct i; simpl in *; try discriminate.
    - injection Hi as <-. exists y'. split; [reflexivity | exact Hxy].
    - apply IH. exact Hi.
  Qed.

  Lemma decode_struct_ranges : forall d size align fields bs1 bs2,
    Forall (fun f => bytes_at (fst f) (size_of (snd f)) bs1 = bytes_at (fst f) (size_of (snd f)) bs2)
           fields ->
    decode (LStruct d size align fields) bs1 = decode (LStruct d size align fields) bs2.
  Proof.
    intros d size align fields bs1 bs2 H. simpl.
    assert (E : map (fun decode_field => decode_field bs1)
                  (map (fun '(offset, f) bs => decode f (bytes_at offset (size_of f) bs)) fields)
                = map (fun decode_field => decode_field bs2)
                  (map (fun '(offset, f) bs => decode f (bytes_at offset (size_of f) bs)) fields)).
    { induction fields as [|[o f] fields IH]; simpl; [reflexivity|].
      inversion H as [|? ? Hf Hrest]; subst. simpl in Hf. rewrite Hf, IH by exact Hrest.
      reflexivity. }
    rewrite E. reflexivity.
  Qed.

  Definition not_vtable (p : pointer_provenance) : Prop :=
    match p with ProvenanceVTable _ => False | _ => True end.

  Lemma provenance_eqb_refl : forall p, not_vtable p -> provenance_eqb p p = true.
  Proof.
    intros [| a | f | t] H; simpl in *; try reflexivity.
    - apply Nat.eqb_refl.
    - apply String.eqb_refl.
    - contradiction.
  Qed.

  Lemma common_provenance_int_bytes : forall n z p,
    not_vtable p -> common_provenance (int_bytes (S n) z (Some p)) = p.
  Proof.
    intros n z p Hp. unfold int_bytes. simpl.
    assert (Hall : forallb (fun c => provenance_eqb p (byte_provenance c))
                     (map (fun b => MByte b (Some p)) (little_endian n (z / 256))) = true).
    { induction (little_endian n (z / 256)) as [|b bs IH]; simpl; [reflexivity|].
      rewrite provenance_eqb_refl by exact Hp. exact IH. }
    rewrite Hall. reflexivity.
  Qed.

  Opaque int_bytes.

  Lemma decode_encode_pointer : forall kind p bs,
    not_vtable (pointer_provenance_of p) ->
    (match pointer_metadata_of p with PointerVTable _ => False | _ => True end) ->
    encode_pointer kind p = Some bs -> decode_pointer kind bs = AccessOk p.
  Proof.
    intros kind [prov address meta] bs Hp Hm H. unfold encode_pointer in H.
    cbn [pointer_address pointer_provenance_of pointer_metadata_of] in *.
    unfold in_word_range in H.
    destruct (0 <=? address)%Z eqn:E1; [|discriminate].
    destruct (address <? 2 ^ 64)%Z eqn:E2; [|discriminate]. simpl in H.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold decode_pointer.
    assert (Ha : int_value (int_bytes pointer_bytes address (Some prov)) = AccessOk address)
      by (apply int_value_int_bytes; rewrite <- word_range_bytes; lia).
    assert (Hc : common_provenance (int_bytes pointer_bytes address (Some prov)) = prov)
      by (apply (common_provenance_int_bytes 7); exact Hp).
    destruct kind, meta as [| n | t]; try discriminate; try contradiction.
    - injection H as <-. rewrite firstn_all2 by (rewrite length_int_bytes; lia).
      rewrite Ha, Hc. reflexivity.
    - match type of H with context [if ?c then _ else _] => destruct c eqn:E3 end; [|discriminate].
      injection H as <-. apply andb_prop in E3 as [E3 E4].
      apply Z.leb_le in E3. apply Z.ltb_lt in E4.
      rewrite firstn_app, length_int_bytes, Nat.sub_diag, firstn_all2 by (rewrite length_int_bytes; lia).
      rewrite skipn_app, length_int_bytes, Nat.sub_diag, skipn_all2 by (rewrite length_int_bytes; lia).
      simpl. rewrite app_nil_r, Ha, Hc. simpl.
      rewrite int_value_int_bytes by (rewrite <- word_range_bytes; lia). simpl.
      rewrite Nat2Z.id. reflexivity.
  Qed.

  Lemma decode_encode : forall l v bs,
    layout_wf l -> vtable_free v = true -> encode l v = Some bs -> decode l bs = AccessOk v.
  Proof.
    intros l. induction l using layout_induction;
      try match goal with IH : Forall _ _ |- _ => rename IH into IHf end;
      intros v bs Hwf Hvt H; cbn [encode] in H.
    - destruct v; try discriminate.
      destruct (int_width_eqb w width) eqn:Ew; [|discriminate].
      destruct (0 <=? bits)%Z eqn:E1; [|discriminate].
      destruct (bits <? width_limit w)%Z eqn:E2; [|discriminate].
      injection H as <-. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      assert (w = width) by (destruct w, width; try reflexivity; discriminate). subst width.
      simpl. rewrite int_value_int_bytes by (rewrite <- width_limit_bytes; lia). reflexivity.
    - destruct v; try discriminate. injection H as <-. destruct value; reflexivity.
    - destruct v; try discriminate. destruct (valid_char value) eqn:Ev; [|discriminate].
      injection H as <-. cbn [decode].
      assert (Hb : (0 <= value <= 1114111)%Z).
      { unfold valid_char in Ev. apply andb_prop in Ev as [Ev _]. apply andb_prop in Ev as [E1 E2].
        apply Z.leb_le in E1. apply Z.leb_le in E2. lia. }
      rewrite int_value_int_bytes by (cbn; lia). cbn [and_then ub_unless]. rewrite Ev. reflexivity.
    - destruct v as [| | | pointer| | |]; try discriminate. simpl.
      simpl in Hvt. rewrite (decode_encode_pointer k pointer bs); [reflexivity| | |exact H];
        destruct (pointer_provenance_of pointer), (pointer_metadata_of pointer); simpl in *;
        solve [exact I | discriminate].
    - destruct v as [| | | pointer| | |]; try discriminate. simpl.
      simpl in Hvt. rewrite (decode_encode_pointer k pointer bs); [reflexivity| | |exact H];
        destruct (pointer_provenance_of pointer), (pointer_metadata_of pointer); simpl in *;
        solve [exact I | discriminate].
    - destruct v; try discriminate. destruct fields as [|]; try discriminate.
      reflexivity.
    - discriminate.
    - destruct v; try discriminate.
      destruct (Nat.eqb_spec (length elements) n) as [Hn|]; [|discriminate].
      destruct (all_some (map (encode l) elements)) as [parts|] eqn:E; [|discriminate].
      injection H as <-. cbn [layout_wf] in Hwf. cbn [decode].
      pose proof (all_some_forall2 _ _ _ _ _ E) as E2.
      assert (Hlens : Forall (fun p => length p = size_of l) parts).
      { eapply forall_of_forall2; [exact E2|]. intros x y Hy. exact (encode_length l x y Hwf Hy). }
      assert (Hlp : length parts = n) by (rewrite <- Hn; symmetry; eapply Forall2_length; exact E2).
      rewrite <- Hlp, chunks_concat by exact Hlens.
      rewrite (all_ok_nth _ _ (decode l) parts elements); [reflexivity | lia |].
      intros i p x Hp Hx.
      destruct (forall2_nth_left _ _ _ _ _ _ _ E2 Hx) as [p' [Hp' Hxp]].
      rewrite Hp in Hp'. injection Hp' as <-.
      apply IHl; [exact Hwf | | exact Hxp].
      simpl in Hvt. rewrite forallb_forall in Hvt. apply Hvt. eapply nth_error_In. exact Hx.
    - destruct (struct_fields d v) as [vs|] eqn:Hvs; [|discriminate].
      assert (Henc : encode (LStruct d size align fields) v = Some bs)
        by (cbn [encode]; rewrite Hvs; exact H).
      assert (Hlen : length vs = length fields).
      { rewrite place_fields_parts in H. destruct (field_parts _ vs) as [parts|] eqn:E; [|discriminate].
        apply field_parts_encoded in E. apply encoded_fields_lengths in E. lia. }
      pose proof (struct_fields_shape d v vs Hvs) as Hshape.
      assert (Hvts : forallb vtable_free vs = true) by (destruct d; subst v; exact Hvt).
      cbn [decode]. rewrite map_map.
      rewrite (all_ok_nth _ _ _ fields vs); [destruct d; subst v; reflexivity | lia |].
      intros i [o f] x Hf Hx. cbn beta iota.
      destruct (struct_field_encode d size align fields v bs vs i o f x Hwf Henc Hvs Hf Hx)
        as [Hwff [_ [_ [_ Hb]]]].
      rewrite Forall_forall in IHf.
      apply (IHf (o, f) (nth_error_In _ _ Hf) x); [exact Hwff | | exact Hb].
      rewrite forallb_forall in Hvts. apply Hvts. eapply nth_error_In. exact Hx.
    - destruct v as [| | | | | |d' k vs]; try discriminate.
      destruct (String.eqb_spec d d') as [<-|]; [|discriminate].
      rewrite nth_error_map in H.
      destruct (nth_error variants k) as [variant|] eqn:Hk; [|discriminate]. cbn [option_map] in H.
      destruct (encode variant (VTuple vs)) as [vb|] eqn:Hvb; [|discriminate].
      injection H as <-.
      pose proof (enum_variants_wf _ _ _ _ _ _ Hwf) as Hvw.
      destruct (variant_of_enum _ _ _ _ _ _ _ _ Hwf Hk) as [fields [-> [Hvwf Hap]]].
      destruct Hwf as [[_ [_ [_ [Htag [Hroom _]]]]] _].
      assert (Hkl : k < length variants) by (apply nth_error_Some; congruence).
      assert (Hvlen : length vb = size) by (rewrite (encode_length _ _ _ Hvwf Hvb); reflexivity).
      cbn [decode].
      rewrite bytes_at_splice_length by (rewrite ?length_int_bytes; lia).
      rewrite int_value_int_bytes by lia. cbn [and_then].
      rewrite Nat2Z.id, nth_error_map, Hk. cbn [option_map].
      rewrite (decode_struct_ranges None size align fields _ vb).
      + rewrite Forall_forall in IHf.
        rewrite (IHf _ (nth_error_In _ _ Hk) (VTuple vs) vb Hvwf Hvt Hvb). reflexivity.
      + unfold ranges in Hap. rewrite Forall_map in Hap. eapply Forall_impl; [|exact Hap].
        intros [o f] Ha. unfold apart in Ha. simpl in *.
        apply bytes_at_splice_apart; rewrite length_int_bytes; lia.
  Qed.

  Transparent int_bytes.

End RoundTrip.

Section Update.

  Definition value_fields (v : runtime_value) : option (list runtime_value) :=
    match v with
    | VTuple vs | VAdt _ _ vs => Some vs
    | _ => None
    end.

  Definition with_fields (v : runtime_value) (vs : list runtime_value) : runtime_value :=
    match v with
    | VTuple _ => VTuple vs
    | VAdt d k _ => VAdt d k vs
    | _ => v
    end.

  Definition set_step (s : step) (v x : runtime_value) : option runtime_value :=
    match s with
    | Field i =>
        match value_fields v with
        | Some vs => option_map (with_fields v) (set_nth i x vs)
        | None => None
        end
    | Elements first count =>
        match v, x with
        | VArray vs, VArray xs => Some (VArray (firstn first vs ++ xs ++ skipn (first + count) vs))
        | _, _ => None
        end
    end.

  Fixpoint set_path (l : layout) (v : runtime_value) (p : list step) (x : runtime_value)
      : option runtime_value :=
    match p with
    | [] => Some x
    | s :: rest =>
        match step_at l v s with
        | Some (_, l', v') =>
            match set_path l' v' rest x with
            | Some v'' => set_step s v v''
            | None => None
            end
        | None => None
        end
    end.

  Lemma nth_error_set_nth : forall (A : Type) (xs ys : list A) i x j,
    set_nth i x xs = Some ys ->
    nth_error ys j = if Nat.eqb i j then Some x else nth_error xs j.
  Proof.
    intros A xs ys i x. revert xs ys. induction i as [|i IH]; intros [|y xs] ys j H;
      simpl in H; try discriminate.
    - injection H as <-. destruct j; reflexivity.
    - destruct (set_nth i x xs) as [rest|] eqn:E; [|discriminate]. injection H as <-.
      destruct j; simpl; [reflexivity | apply IH; exact E].
  Qed.

  Lemma set_nth_some : forall (A : Type) (xs : list A) i x,
    i < length xs -> exists ys, set_nth i x xs = Some ys /\ length ys = length xs.
  Proof.
    intros A xs i x. revert xs. induction i as [|i IH]; intros [|y xs] H; simpl in *; try lia.
    - exists (x :: xs). split; reflexivity.
    - destruct (IH xs ltac:(lia)) as [ys [E Hl]]. rewrite E. exists (y :: ys).
      split; [reflexivity | simpl; lia].
  Qed.

  Lemma splice_all_replace : forall parts parts' bytes i o b b',
    parts_inside (length bytes) parts -> pairwise_apart (part_ranges parts) ->
    nth_error parts i = Some (o, b) -> length b' = length b ->
    (forall j, nth_error parts' j = if Nat.eqb i j then Some (o, b') else nth_error parts j) ->
    splice_all parts' bytes = splice o b' (splice_all parts bytes).
  Proof.
    induction parts as [|[o0 b0] parts IH]; intros parts' bytes i o b b' Hin Hap Hi Hl Hj;
      [destruct i; discriminate|].
    destruct parts' as [|[o0' b0'] parts'].
    { specialize (Hj 0). destruct i; discriminate. }
    inversion Hin as [|? ? Hp Hrest]; subst. simpl in Hp. destruct Hap as [Hhead Htail].
    destruct i as [|i]; simpl in Hi.
    - injection Hi as <- <-.
      pose proof (Hj 0) as H0. simpl in H0. injection H0 as -> ->.
      assert (Hrest' : parts' = parts).
      { apply nth_error_ext. intros j. exact (Hj (S j)). }
      subst parts'. simpl.
      assert (Hap' : Forall (fun r => apart o0 (length b') (fst r) (snd r)) (part_ranges parts)).
      { eapply Forall_impl; [|exact Hhead]. intros r Hr. unfold apart in *. rewrite Hl. exact Hr. }
      rewrite (splice_all_splice_apart parts bytes o0 b') by (exact Hrest || lia || exact Hap').
      rewrite (splice_all_splice_apart parts bytes o0 b0) by (exact Hrest || lia || exact Hhead).
      rewrite splice_splice_same; [reflexivity | exact (eq_sym Hl) |].
      rewrite length_splice_all by exact Hrest. exact Hp.
    - pose proof (Hj 0) as H0. simpl in H0. injection H0 as -> ->. simpl.
      apply (IH parts' _ i o b b');
        [rewrite length_splice by exact Hp; exact Hrest | exact Htail | exact Hi | exact Hl |].
      intros j. exact (Hj (S j)).
  Qed.

  Lemma encoded_fields_set : forall fields vs parts i o f y bnew vs' parts',
    encoded_fields fields vs parts -> nth_error fields i = Some (o, f) -> encode f y = Some bnew ->
    set_nth i y vs = Some vs' -> set_nth i (o, bnew) parts = Some parts' ->
    encoded_fields fields vs' parts'.
  Proof.
    intros fields vs parts i o f y bnew vs' parts' H. revert i vs' parts'.
    induction H as [|o0 f0 v b fields vs parts Hb Hrest IH]; intros i vs' parts' Hf Hy Hvs Hps;
      [destruct i; discriminate|].
    destruct i as [|i]; simpl in *.
    - injection Hf as <- <-. injection Hvs as <-. injection Hps as <-. constructor; assumption.
    - destruct (set_nth i y vs) as [rest|] eqn:E1; [|discriminate].
      destruct (set_nth i (o, bnew) parts) as [prest|] eqn:E2; [|discriminate].
      injection Hvs as <-. injection Hps as <-. constructor; [exact Hb|].
      eapply IH; eassumption.
  Qed.

  Lemma struct_update : forall d size align fields v bs vs i o f y bnew,
    layout_wf (LStruct d size align fields) -> encode (LStruct d size align fields) v = Some bs ->
    struct_fields d v = Some vs -> nth_error fields i = Some (o, f) -> encode f y = Some bnew ->
    exists vs', set_nth i y vs = Some vs'
      /\ encode (LStruct d size align fields) (with_fields v vs') = Some (splice o bnew bs).
  Proof.
    intros d size align fields v bs vs i o f y bnew Hwf H Hvs Hf Hy.
    pose proof (struct_fields_wf _ _ _ _ Hwf) as Hfw.
    destruct Hwf as [[_ [_ [_ [Hfits Hapart]]]] _].
    pose proof (struct_fields_shape d v vs Hvs) as Hshape.
    cbn [encode] in H. rewrite Hvs, place_fields_parts in H.
    destruct (field_parts _ vs) as [parts|] eqn:E; [|discriminate].
    injection H as <-. apply field_parts_encoded in E.
    destruct (encoded_fields_lengths _ _ _ E) as [Hlv Hlp].
    assert (Hi : i < length fields) by (apply nth_error_Some; congruence).
    destruct (set_nth_some _ vs i y ltac:(lia)) as [vs' [Hvs' Hlv']].
    destruct (set_nth_some _ parts i (o, bnew) ltac:(lia)) as [parts' [Hps' _]].
    destruct (encoded_fields_nth _ _ _ _ _ _ E Hf) as [x [b [Hx [Hb Hp]]]].
    assert (Hin : In (o, f) fields) by (eapply nth_error_In; exact Hf).
    rewrite Forall_forall in Hfw. pose proof (Hfw _ Hin) as Hwff. simpl in Hwff.
    exists vs'. split; [exact Hvs'|].
    assert (Hvs2 : struct_fields d (with_fields v vs') = Some vs')
      by (destruct d; subst v; simpl; rewrite ?String.eqb_refl; reflexivity).
    cbn [encode]. rewrite Hvs2, place_fields_parts.
    rewrite (encoded_field_parts fields vs' parts')
      by exact (encoded_fields_set fields vs parts i o f y bnew vs' parts' E Hf Hy Hvs' Hps').
    simpl. f_equal.
    apply (splice_all_replace parts parts' _ i o b bnew).
    - rewrite repeat_length. eapply encoded_inside; [exact E | apply Forall_forall; exact Hfw |].
      eapply Forall_impl; [|exact Hfits]. intros g [Hg _]. exact Hg.
    - rewrite (encoded_ranges _ _ _ E) by (apply Forall_forall; exact Hfw). exact Hapart.
    - exact Hp.
    - rewrite (encode_length f y bnew Hwff Hy), (encode_length f x b Hwff Hb). reflexivity.
    - intros j. apply nth_error_set_nth. exact Hps'.
  Qed.

  Lemma all_some_app : forall (A B : Type) (g : A -> option B) xs ys xs' ys',
    all_some (map g xs) = Some xs' -> all_some (map g ys) = Some ys' ->
    all_some (map g (xs ++ ys)) = Some (xs' ++ ys').
  Proof.
    intros A B g xs. induction xs as [|x xs IH]; intros ys xs' ys' H1 H2; simpl in *.
    - injection H1 as <-. exact H2.
    - destruct (g x) as [b|]; [|discriminate].
      destruct (all_some (map g xs)) as [rest|] eqn:E; [|discriminate].
      injection H1 as <-. rewrite (IH ys rest ys' eq_refl H2). reflexivity.
  Qed.

  Lemma all_some_firstn : forall (A B : Type) (g : A -> option B) xs ys c,
    all_some (map g xs) = Some ys -> all_some (map g (firstn c xs)) = Some (firstn c ys).
  Proof.
    intros A B g xs ys c H. pose proof (all_some_firstn_skipn A B g xs ys 0 c H) as H0.
    rewrite !skipn_O in H0. exact H0.
  Qed.

  Lemma all_some_skipn : forall (A B : Type) (g : A -> option B) xs ys j,
    all_some (map g xs) = Some ys -> all_some (map g (skipn j xs)) = Some (skipn j ys).
  Proof.
    intros A B g xs. induction xs as [|x xs IH]; intros ys j H; simpl in H.
    - injection H as <-. rewrite !skipn_nil. reflexivity.
    - destruct (g x) as [y|] eqn:Eg; [|discriminate].
      destruct (all_some (map g xs)) as [rest|] eqn:E; [|discriminate].
      injection H as <-. destruct j as [|j]; simpl; [rewrite Eg, E; reflexivity | apply IH; reflexivity].
  Qed.

  Lemma step_update : forall l v s o l1 v1 bs y bnew,
    layout_wf l -> encode l v = Some bs -> step_at l v s = Some (o, l1, v1) ->
    encode l1 y = Some bnew ->
    exists v2, set_step s v y = Some v2 /\ encode l v2 = Some (splice o bnew bs).
  Proof.
    intros l v [i|first count] o l1 v1 bs y bnew Hwf H Hs Hy; simpl in Hs.
    - unfold field_at in Hs. destruct l; try discriminate.
      + destruct (struct_fields declaration v) as [vs|] eqn:Hvs; [|discriminate].
        destruct (nth_error fields i) as [[o0 f]|] eqn:Hf; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-.
        destruct (struct_update _ _ _ _ v bs vs i o0 f y bnew Hwf H Hvs Hf Hy) as [vs' [Hvs' Henc]].
        exists (with_fields v vs'). split; [|exact Henc].
        pose proof (struct_fields_shape _ v vs Hvs) as Hshape.
        simpl. destruct declaration; subst v; simpl; rewrite Hvs'; reflexivity.
      + destruct v as [| | | | | |d' k vs]; try discriminate.
        destruct (String.eqb_spec declaration d') as [<-|]; [|discriminate].
        destruct (nth_error variants k) as [variant|] eqn:Hk; [|discriminate].
        destruct (variant_of_enum _ _ _ _ _ _ _ _ Hwf Hk) as [fields [-> [Hvwf Hap]]].
        destruct (nth_error fields i) as [[o0 f]|] eqn:Hf; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-.
        cbn [encode] in H. rewrite String.eqb_refl, nth_error_map, Hk in H. cbn [option_map] in H.
        destruct (encode (LStruct None size align fields) (VTuple vs)) as [vb|] eqn:Hvb;
          [|discriminate].
        injection H as <-.
        destruct (struct_update _ _ _ _ (VTuple vs) vb vs i o0 f y bnew Hvwf Hvb eq_refl Hf Hy)
          as [vs' [Hvs' Henc]].
        exists (VAdt declaration k vs'). split; [simpl; rewrite Hvs'; reflexivity|].
        cbn [encode]. rewrite String.eqb_refl, nth_error_map, Hk. cbn [option_map].
        change (with_fields (VTuple vs) vs') with (VTuple vs') in Henc.
        rewrite Henc. cbn [option_map]. f_equal.
        pose proof (struct_field_encode _ _ _ _ _ _ _ _ _ _ _ Hvwf Hvb eq_refl Hf Hx)
          as [Hwff [Hfit _]].
        destruct Hwf as [[_ [_ [_ [Htag _]]]] _].
        assert (Hvl : length vb = size) by (rewrite (encode_length _ _ _ Hvwf Hvb); reflexivity).
        assert (Hyl : length bnew = size_of f) by exact (encode_length _ _ _ Hwff Hy).
        assert (Hin : In (o0, size_of f) (ranges fields)).
        { unfold ranges. apply in_map_iff. exists (o0, f). split; [reflexivity|].
          eapply nth_error_In. exact Hf. }
        rewrite Forall_forall in Hap. specialize (Hap _ Hin). unfold apart in Hap. simpl in Hap.
        apply splice_comm; rewrite ?length_int_bytes; lia.
    - unfold elements_at in Hs. destruct l; try discriminate. destruct v; try discriminate.
      destruct (Nat.leb_spec (first + count) count0) as [Hle|]; [|discriminate].
      injection Hs as <- <- <-. cbn [encode] in H, Hy.
      destruct (Nat.eqb_spec (length elements) count0) as [Hn|]; [|discriminate].
      destruct (all_some (map (encode l) elements)) as [parts|] eqn:E; [|discriminate].
      injection H as <-. cbn [layout_wf] in Hwf.
      destruct y as [| | | | ys | |]; try discriminate.
      destruct (Nat.eqb_spec (length ys) count) as [Hyn|]; [|discriminate].
      destruct (all_some (map (encode l) ys)) as [yparts|] eqn:Ey; [|discriminate].
      injection Hy as <-.
      exists (VArray (firstn first elements ++ ys ++ skipn (first + count) elements)).
      split; [reflexivity|].
      pose proof (all_some_forall2 _ _ _ _ _ E) as E2.
      pose proof (all_some_forall2 _ _ _ _ _ Ey) as Ey2.
      assert (Hlens : Forall (fun p => length p = size_of l) parts).
      { eapply forall_of_forall2; [exact E2|]. intros x y Hxy. exact (encode_length l x y Hwf Hxy). }
      assert (Hylens : Forall (fun p => length p = size_of l) yparts).
      { eapply forall_of_forall2; [exact Ey2|]. intros x y Hxy. exact (encode_length l x y Hwf Hxy). }
      assert (Hlp : length parts = count0)
        by (rewrite <- Hn; symmetry; eapply Forall2_length; exact E2).
      assert (Hlyp : length yparts = count)
        by (rewrite <- Hyn; symmetry; eapply Forall2_length; exact Ey2).
      cbn [encode].
      rewrite !length_app, length_firstn, length_skipn, Nat.min_l by lia.
      replace (first + (length ys + (length elements - (first + count)))) with count0 by lia.
      rewrite Nat.eqb_refl.
      rewrite (all_some_app _ _ _ _ _ (firstn first parts) (yparts ++ skipn (first + count) parts)).
      + simpl. f_equal. unfold splice.
        rewrite !concat_app.
        rewrite <- (firstn_concat parts (size_of l) first) by (exact Hlens || lia).
        rewrite (length_concat_uniform yparts (size_of l) Hylens), Hlyp.
        replace (first * size_of l + count * size_of l) with ((first + count) * size_of l) by lia.
        rewrite (skipn_concat parts (size_of l) (first + count)) by (exact Hlens || lia).
        reflexivity.
      + apply all_some_firstn. exact E.
      + apply all_some_app; [exact Ey|]. apply all_some_skipn. exact E.
  Qed.

  Lemma set_path_encode : forall p l v o l' v' x bs bx,
    layout_wf l -> encode l v = Some bs -> at_path l v p = Some (o, l', v') ->
    encode l' x = Some bx ->
    exists v2, set_path l v p x = Some v2 /\ encode l v2 = Some (splice o bx bs).
  Proof.
    induction p as [|s p IH]; intros l v o l' v' x bs bx Hwf H Hp Hx; simpl in Hp.
    - injection Hp as <- <- <-. exists x. split; [reflexivity|].
      rewrite Hx. f_equal. symmetry. apply splice_whole.
      rewrite (encode_length _ _ _ Hwf Hx), (encode_length _ _ _ Hwf H). reflexivity.
    - destruct (step_at l v s) as [[[o1 l1] v1]|] eqn:Hs; [|discriminate].
      destruct (at_path l1 v1 p) as [[[o2 l2] v2]|] eqn:Hp2; [|discriminate].
      injection Hp as <- <- <-.
      destruct (step_encode l v s o1 l1 v1 bs Hwf H Hs) as [Hwf1 [Hfit1 [_ [_ H1]]]].
      destruct (IH l1 v1 o2 l2 v2 x _ bx Hwf1 H1 Hp2 Hx) as [v1' [Hset Henc1]].
      destruct (step_update l v s o1 l1 v1 bs v1' _ Hwf H Hs Henc1) as [v2' [Hstep Henc2]].
      exists v2'. simpl. rewrite Hs, Hset. split; [exact Hstep|].
      rewrite Henc2. f_equal.
      destruct (at_path_encode p l1 v1 o2 l2 v2 _ Hwf1 H1 Hp2) as [Hwf2 [Hfit2 _]].
      apply splice_inside.
      + rewrite (encode_length _ _ _ Hwf H). exact Hfit1.
      + rewrite (encode_length _ _ _ Hwf2 Hx). exact Hfit2.
  Qed.

End Update.

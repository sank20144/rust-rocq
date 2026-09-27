From RustRocq Require Import Syntax Subst LayoutAlg Memory Proof.Encoding.
From Stdlib Require Import Bool List String ZArith Lia.
Import ListNotations.

Notation length := List.length.

Local Open Scope string_scope.
Local Open Scope list_scope.

Section Fuel.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Lemma all_some_map_ext : forall (A B : Type) (f g : A -> option B) xs ys,
    (forall x y, In x xs -> f x = Some y -> g x = Some y) ->
    all_some (map f xs) = Some ys -> all_some (map g xs) = Some ys.
  Proof.
    intros A B f g. induction xs as [|x xs IH]; intros ys Himp H; simpl in *; [exact H|].
    destruct (f x) as [y|] eqn:E; [|discriminate].
    destruct (all_some (map f xs)) as [rest|] eqn:E'; [|discriminate].
    rewrite (Himp x y (or_introl eq_refl) E).
    rewrite (IH rest (fun x' y' Hin => Himp x' y' (or_intror Hin)) eq_refl). exact H.
  Qed.

  Lemma layout_of_fuel_mono : forall n t l,
    layout_of_fuel adts n t = Some l -> forall m, n <= m -> layout_of_fuel adts m t = Some l.
  Proof.
    induction n as [|n IH]; intros t l H m Hle; [discriminate|].
    destruct m as [|m]; [lia|].
    assert (Hall : forall ts ls, all_some (map (layout_of_fuel adts n) ts) = Some ls ->
                                 all_some (map (layout_of_fuel adts m) ts) = Some ls).
    { intros ts ls. apply all_some_map_ext. intros x y _ Hy. apply (IH x y Hy m). lia. }
    assert (Hall2 : forall (vs : list variant_def) args ls,
      all_some (map (fun v => all_some (map (layout_of_fuel adts n) (variant_field_tys args v))) vs)
        = Some ls ->
      all_some (map (fun v => all_some (map (layout_of_fuel adts m) (variant_field_tys args v))) vs)
        = Some ls).
    { intros vs args ls. apply all_some_map_ext. intros x y _ Hy. apply Hall. exact Hy. }
    destruct t; cbn [layout_of_fuel] in H |- *; try exact H.
    - destruct (find_adt adts path) as [d|]; [|discriminate].
      destruct (ad_kind d), (ad_variants d) as [|v [|v' vs]]; try discriminate.
      + destruct (all_some (map (layout_of_fuel adts n) (variant_field_tys args v)))
          as [fields|] eqn:E; [|discriminate].
        rewrite (Hall _ _ E). exact H.
      + exact H.
      + destruct (all_some (map _ (v :: nil))) as [variants|] eqn:E; [|discriminate].
        rewrite (Hall2 _ _ _ E). exact H.
      + destruct (all_some (map _ (v :: v' :: vs))) as [variants|] eqn:E; [|discriminate].
        rewrite (Hall2 _ _ _ E). exact H.
    - destruct (layout_of_fuel adts n t) as [le|] eqn:E; [|discriminate].
      rewrite (IH t le E m ltac:(lia)). exact H.
    - apply (IH _ _ H m). lia.
    - destruct (closure_upvars args) as [u|]; [|discriminate]. apply (IH _ _ H m). lia.
    - destruct elems as [|t ts]; [exact H|].
      destruct (all_some _) as [fields|] eqn:E; [|discriminate].
      rewrite (Hall _ _ E). exact H.
  Qed.

  Lemma layout_of_from_fuel : forall n t l,
    n <= 64 -> layout_of_fuel adts n t = Some l -> layout_of adts t = Some l.
  Proof. intros n t l Hle H. unfold layout_of. exact (layout_of_fuel_mono n t l H 64 Hle). Qed.

End Fuel.

Section Inversion.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Lemma layout_of_eq : forall t, layout_of adts t = layout_of_fuel adts 64 t.
  Proof. intros t. reflexivity. Qed.

  Lemma layout_of_fuel_struct : forall n path args d v,
    find_adt adts path = Some d -> ad_kind d = AkStruct -> ad_variants d = [v] ->
    layout_of_fuel adts (S n) (TAdt path args) =
      match all_some (map (layout_of_fuel adts n) (variant_field_tys args v)) with
      | Some fields => struct_layout (Some path) path (reprs_of (ad_repr d)) fields
      | None => None
      end.
  Proof. intros n path args d v Hd Hk Hv. cbn [layout_of_fuel]. rewrite Hd, Hk, Hv. reflexivity. Qed.

  Lemma layout_of_fuel_enum : forall n path args d,
    find_adt adts path = Some d -> ad_kind d = AkEnum ->
    layout_of_fuel adts (S n) (TAdt path args) =
      match all_some (map (fun v => all_some (map (layout_of_fuel adts n) (variant_field_tys args v)))
                          (ad_variants d)) with
      | Some variants => enum_layout_of path (reprs_of (ad_repr d)) variants
      | None => None
      end.
  Proof.
    intros n path args d Hd Hk. cbn [layout_of_fuel]. rewrite Hd, Hk.
    destruct (ad_variants d) as [|v [|v' vs]]; reflexivity.
  Qed.

  Lemma layout_of_fuel_tuple : forall n t ts,
    layout_of_fuel adts (S n) (TTuple (t :: ts)) =
      match all_some (map (layout_of_fuel adts n) (t :: ts)) with
      | Some fields => struct_layout None "" [] fields
      | None => None
      end.
  Proof. reflexivity. Qed.

  Lemma forall2_layouts : forall n tys ls,
    n <= 64 -> all_some (map (layout_of_fuel adts n) tys) = Some ls ->
    Forall2 (fun t l => layout_of adts t = Some l) tys ls.
  Proof.
    intros n tys ls Hle H. apply all_some_forall2 in H.
    induction H; constructor; [eapply layout_of_from_fuel; eassumption | assumption].
  Qed.

  Lemma struct_layout_inv : forall declaration name reprs fields L,
    struct_layout declaration name reprs fields = Some L ->
    exists a, struct_alg name (map size_align_of fields) reprs = Some a
      /\ L = LStruct declaration (ag_size a) (ag_align a) (combine (ag_offsets a) fields)
      /\ length (ag_offsets a) = length fields.
  Proof.
    intros declaration name reprs fields L H. unfold struct_layout in H.
    destruct (struct_alg name (map size_align_of fields) reprs) as [a|] eqn:E; [|discriminate].
    injection H as <-. exists a. split; [reflexivity|]. split; [reflexivity|].
    destruct (struct_alg_placed _ _ _ _ E) as [Hl _]. rewrite length_map in Hl. exact Hl.
  Qed.

  Lemma layout_of_struct : forall path args d v L,
    find_adt adts path = Some d -> ad_kind d = AkStruct -> ad_variants d = [v] ->
    layout_of adts (TAdt path args) = Some L ->
    exists a fls, struct_alg path (map size_align_of fls) (reprs_of (ad_repr d)) = Some a
      /\ L = LStruct (Some path) (ag_size a) (ag_align a) (combine (ag_offsets a) fls)
      /\ length (ag_offsets a) = length fls
      /\ Forall2 (fun t l => layout_of adts t = Some l) (variant_field_tys args v) fls.
  Proof.
    intros path args d v L Hd Hk Hv H. rewrite layout_of_eq in H.
    rewrite (layout_of_fuel_struct 63 path args d v Hd Hk Hv) in H.
    destruct (all_some (map (layout_of_fuel adts 63) (variant_field_tys args v)))
      as [fls|] eqn:E; [|discriminate].
    destruct (struct_layout_inv _ _ _ _ _ H) as [a [Ha [HL Hlen]]].
    exists a, fls. split; [exact Ha|]. split; [exact HL|]. split; [exact Hlen|].
    eapply forall2_layouts; [|exact E]. lia.
  Qed.

  Lemma layout_of_tuple : forall t ts L,
    layout_of adts (TTuple (t :: ts)) = Some L ->
    exists a fls, struct_alg "" (map size_align_of fls) [] = Some a
      /\ L = LStruct None (ag_size a) (ag_align a) (combine (ag_offsets a) fls)
      /\ length (ag_offsets a) = length fls
      /\ Forall2 (fun t l => layout_of adts t = Some l) (t :: ts) fls.
  Proof.
    intros t ts L H. rewrite layout_of_eq, layout_of_fuel_tuple in H.
    destruct (all_some (map (layout_of_fuel adts 63) (t :: ts))) as [fls|] eqn:E; [|discriminate].
    destruct (struct_layout_inv _ _ _ _ _ H) as [a [Ha [HL Hlen]]].
    exists a, fls. split; [exact Ha|]. split; [exact HL|]. split; [exact Hlen|].
    eapply forall2_layouts; [|exact E]. lia.
  Qed.

  Lemma layout_of_enum : forall path args d L,
    find_adt adts path = Some d -> ad_kind d = AkEnum ->
    layout_of adts (TAdt path args) = Some L ->
    exists e vls, enum_alg path (map (map size_align_of) vls) (reprs_of (ad_repr d)) = Some e
      /\ L = LEnum path (en_size e) (en_align e) (en_tag_offset e) (scalar_bytes (en_tag e))
               (map (fun '(placed, fields) =>
                       LStruct None (en_size e) (en_align e) (combine (ag_offsets placed) fields))
                    (combine (en_variants e) vls))
      /\ length (en_variants e) = length vls
      /\ Forall2 (fun v ls => Forall2 (fun t l => layout_of adts t = Some l)
                                      (variant_field_tys args v) ls) (ad_variants d) vls
      /\ Forall2 (fun p ls => length (ag_offsets p) = length ls) (en_variants e) vls.
  Proof.
    intros path args d L Hd Hk H. rewrite layout_of_eq in H.
    rewrite (layout_of_fuel_enum 63 path args d Hd Hk) in H.
    destruct (all_some _) as [vls|] eqn:E; [|discriminate].
    unfold enum_layout_of in H.
    destruct (enum_alg path (map (map size_align_of) vls) (reprs_of (ad_repr d))) as [e|] eqn:Ee;
      [|discriminate].
    injection H as <-.
    destruct (enum_alg_variants _ _ _ _ Ee) as [Hlen Hpl]. rewrite length_map in Hlen.
    exists e, vls. split; [exact Ee|]. split; [reflexivity|]. split; [exact Hlen|].
    split.
    - apply all_some_forall2 in E. eapply Forall2_impl; [|exact E].
      intros v ls Hv. eapply forall2_layouts; [|exact Hv]. lia.
    - clear -Hpl. remember (map (map size_align_of) vls) as svs eqn:Hsvs.
      revert vls Hsvs. induction Hpl as [|fs p svs ps Hp Hrest IH]; intros vls Hsvs;
        destruct vls as [|ls vls]; simpl in Hsvs; try discriminate; constructor.
      + injection Hsvs as -> _. destruct Hp as [[Hl _] _]. rewrite length_map in Hl. exact Hl.
      + injection Hsvs as _ ->. apply IH. reflexivity.
  Qed.

End Inversion.

From RustRocq Require Import Syntax LayoutAlg Memory Proof.Bytes Proof.Encoding.
From Stdlib Require Import Bool List ZArith Lia.
Import ListNotations.

Local Open Scope list_scope.

Inductive cell :=
  | Holds (t : ty) (v : runtime_value) (holes : list (list step))
  | Fresh (t : ty)
  | Freed (t : ty)
  | Other (al : allocation).

Section Holes.

  Fixpoint punch (l : layout) (v : runtime_value) (holes : list (list step)) (bs : list mbyte)
      : list mbyte :=
    match holes with
    | [] => bs
    | p :: rest =>
        match at_path l v p with
        | Some (o, l', _) => splice o (repeat MUninit (size_of l')) (punch l v rest bs)
        | None => punch l v rest bs
        end
    end.

  Definition apart_from_holes (l : layout) (v : runtime_value) (holes : list (list step))
      (o s : nat) : Prop :=
    Forall (fun q => match at_path l v q with
                     | Some (oq, lq, _) => apart o s oq (size_of lq)
                     | None => True
                     end) holes.

  Lemma length_punch : forall l v holes bs,
    layout_wf l -> encode l v = Some bs -> length (punch l v holes bs) = length bs.
  Proof.
    intros l v holes bs Hwf H. induction holes as [|p holes IH]; simpl; [reflexivity|].
    destruct (at_path l v p) as [[[o l'] v']|] eqn:E; [|exact IH].
    destruct (at_path_encode p l v o l' v' bs Hwf H E) as [_ [Hfit _]].
    rewrite length_splice; [exact IH|].
    rewrite repeat_length, IH, (encode_length l v bs Hwf H). exact Hfit.
  Qed.

  Lemma bytes_at_punch : forall l v holes bs o s,
    layout_wf l -> encode l v = Some bs -> apart_from_holes l v holes o s ->
    bytes_at o s (punch l v holes bs) = bytes_at o s bs.
  Proof.
    intros l v holes bs o s Hwf H Hap. induction holes as [|p holes IH]; simpl; [reflexivity|].
    inversion Hap as [|? ? Hp Hrest]; subst.
    destruct (at_path l v p) as [[[oq lq] vq]|] eqn:E; [|exact (IH Hrest)].
    destruct (at_path_encode p l v oq lq vq bs Hwf H E) as [_ [Hfit _]].
    rewrite bytes_at_splice_apart; [exact (IH Hrest)| |].
    - rewrite repeat_length, length_punch, (encode_length l v bs Hwf H) by assumption. exact Hfit.
    - rewrite repeat_length. unfold apart in Hp. lia.
  Qed.

End Holes.

Section Values.

  Lemma forallb_nth : forall (A : Type) (f : A -> bool) xs i x,
    forallb f xs = true -> nth_error xs i = Some x -> f x = true.
  Proof.
    intros A f xs i x H Hx. rewrite forallb_forall in H. apply H. eapply nth_error_In. exact Hx.
  Qed.

  Lemma forallb_firstn : forall (A : Type) (f : A -> bool) c xs,
    forallb f xs = true -> forallb f (firstn c xs) = true.
  Proof.
    intros A f c. induction c as [|c IH]; intros [|x xs] H; simpl in *; auto.
    apply andb_prop in H as [H1 H2]. rewrite H1, IH by exact H2. reflexivity.
  Qed.

  Lemma forallb_skipn : forall (A : Type) (f : A -> bool) j xs,
    forallb f xs = true -> forallb f (skipn j xs) = true.
  Proof.
    intros A f j. induction j as [|j IH]; intros [|x xs] H; simpl in *; auto.
    apply andb_prop in H as [_ H2]. apply IH. exact H2.
  Qed.

  Lemma forallb_app_true : forall (A : Type) (f : A -> bool) xs ys,
    forallb f xs = true -> forallb f ys = true -> forallb f (xs ++ ys) = true.
  Proof. intros A f xs ys H1 H2. rewrite forallb_app, H1, H2. reflexivity. Qed.

  Lemma forallb_set_nth : forall (A : Type) (f : A -> bool) xs ys i x,
    forallb f xs = true -> f x = true -> set_nth i x xs = Some ys -> forallb f ys = true.
  Proof.
    intros A f xs ys i x H Hx Hs. rewrite forallb_forall in *. intros y Hy.
    apply In_nth_error in Hy as [j Hj]. rewrite (nth_error_set_nth _ xs ys i x j Hs) in Hj.
    destruct (Nat.eqb i j).
    - injection Hj as <-. exact Hx.
    - apply H. eapply nth_error_In. exact Hj.
  Qed.

  Lemma step_vtable_free : forall l v s o l' v',
    step_at l v s = Some (o, l', v') -> vtable_free v = true -> vtable_free v' = true.
  Proof.
    intros l v [i|first count] o l' v' Hs Hv; simpl in Hs.
    - unfold field_at in Hs. destruct l; try discriminate.
      + destruct (struct_fields declaration v) as [vs|] eqn:Hvs; [|discriminate].
        pose proof (struct_fields_shape _ _ _ Hvs) as Hsh.
        destruct (nth_error fields i) as [[o0 f]|]; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-.
        destruct declaration; subst v; simpl in Hv; eapply forallb_nth; eassumption.
      + destruct v as [| | | | | |d' k vs]; try discriminate.
        destruct (String.eqb declaration d'); [|discriminate].
        destruct (nth_error variants k) as [[| | | | | | | |vd vsize valign vfields|]|];
          try discriminate.
        destruct vd; [discriminate|].
        destruct (nth_error vfields i) as [[o0 f]|]; [|discriminate].
        destruct (nth_error vs i) as [x|] eqn:Hx; [|discriminate].
        injection Hs as <- <- <-. simpl in Hv. eapply forallb_nth; eassumption.
    - unfold elements_at in Hs. destruct l, v; try discriminate.
      destruct (_ <=? _); [|discriminate]. injection Hs as <- <- <-.
      simpl in *. apply forallb_firstn, forallb_skipn. exact Hv.
  Qed.

  Lemma at_path_vtable_free : forall p l v o l' v',
    at_path l v p = Some (o, l', v') -> vtable_free v = true -> vtable_free v' = true.
  Proof.
    induction p as [|s p IH]; intros l v o l' v' H Hv; simpl in H.
    - injection H as <- <- <-. exact Hv.
    - destruct (step_at l v s) as [[[o1 l1] v1]|] eqn:Hs; [|discriminate].
      destruct (at_path l1 v1 p) as [[[o2 l2] v2]|] eqn:Hp; [|discriminate].
      injection H as <- <- <-.
      eapply IH; [exact Hp | eapply step_vtable_free; eassumption].
  Qed.

  Lemma set_step_vtable_free : forall s v x v2,
    set_step s v x = Some v2 -> vtable_free v = true -> vtable_free x = true ->
    vtable_free v2 = true.
  Proof.
    intros [i|first count] v x v2 H Hv Hx; simpl in H.
    - destruct v as [| | | | |vs|d k vs]; simpl in H; try discriminate;
        destruct (set_nth i x vs) as [vs'|] eqn:E; try discriminate;
        injection H as <-; simpl in *; eapply forallb_set_nth; eassumption.
    - destruct v, x; try discriminate. injection H as <-. simpl in *.
      apply forallb_app_true; [apply forallb_firstn; exact Hv|].
      apply forallb_app_true; [exact Hx | apply forallb_skipn; exact Hv].
  Qed.

  Lemma set_path_vtable_free : forall p l v x v2,
    set_path l v p x = Some v2 -> vtable_free v = true -> vtable_free x = true ->
    vtable_free v2 = true.
  Proof.
    induction p as [|s p IH]; intros l v x v2 H Hv Hx; simpl in H.
    - injection H as <-. exact Hx.
    - destruct (step_at l v s) as [[[o1 l1] v1]|] eqn:Hs; [|discriminate].
      destruct (set_path l1 v1 p x) as [v1'|] eqn:Hp; [|discriminate].
      eapply set_step_vtable_free; [exact H | exact Hv|].
      eapply IH; [exact Hp | eapply step_vtable_free; eassumption | exact Hx].
  Qed.

End Values.

Section Models.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition cell_model (c : cell) (al : allocation) : Prop :=
    match c with
    | Holds t v holes =>
        exists l bs, layout_of adts t = Some l /\ encode l v = Some bs /\ vtable_free v = true
          /\ al = AllocationData (size_of l) (align_of l) (punch l v holes bs) true
    | Fresh t =>
        exists l, layout_of adts t = Some l
          /\ al = AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) true
    | Freed t =>
        exists l, layout_of adts t = Some l
          /\ al = AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) false
    | Other al' => al = al'
    end.

  Definition models (m : memory_state) (cells : list cell) : Prop := Forall2 cell_model cells m.

  Lemma models_nth : forall m cells a c,
    models m cells -> nth_error cells a = Some c ->
    exists al, nth_error m a = Some al /\ cell_model c al.
  Proof.
    intros m cells a c H. revert a. induction H as [|c' al cells' m' Hc Hrest IH]; intros a Ha;
      destruct a; simpl in *; try discriminate.
    - injection Ha as <-. exists al. split; [reflexivity | exact Hc].
    - apply IH. exact Ha.
  Qed.

  Lemma models_length : forall m cells, models m cells -> length m = length cells.
  Proof. intros m cells H. symmetry. eapply Forall2_length. exact H. Qed.

  Lemma models_set : forall m cells a c al m' ,
    models m cells -> a < length cells -> cell_model c al -> set_nth a al m = Some m' ->
    exists cells', set_nth a c cells = Some cells' /\ models m' cells'.
  Proof.
    intros m cells a c al m' H. revert a m'.
    induction H as [|c0 al0 cells0 m0 Hc Hrest IH]; intros a m' Ha Hcal Hs; simpl in *; [lia|].
    destruct a as [|a]; simpl in Hs.
    - injection Hs as <-. exists (c :: cells0). split; [reflexivity | constructor; assumption].
    - destruct (set_nth a al m0) as [rest|] eqn:E; [|discriminate]. injection Hs as <-.
      destruct (IH a rest ltac:(lia) Hcal E) as [cells' [E' Hm]].
      exists (c0 :: cells'). simpl. rewrite E'. split; [reflexivity | constructor; assumption].
  Qed.

  Lemma models_app : forall m cells c al,
    models m cells -> cell_model c al -> models (m ++ [al]) (cells ++ [c]).
  Proof. intros m cells c al H Hc. apply Forall2_app; [exact H | constructor; [exact Hc | constructor]]. Qed.

  Lemma holds_allocation : forall m cells a t v holes,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    exists l bs, layout_of adts t = Some l /\ encode l v = Some bs /\ vtable_free v = true
      /\ layout_wf l
      /\ nth_error m a = Some (AllocationData (size_of l) (align_of l) (punch l v holes bs) true).
  Proof.
    intros m cells a t v holes H Ha. destruct (models_nth m cells a _ H Ha) as [al [Hal Hc]].
    destruct Hc as [l [bs [Hl [Hbs [Hvt ->]]]]].
    exists l, bs. repeat split; try assumption. eapply layout_of_wf. exact Hl.
  Qed.

  Lemma live_allocation_holds : forall m cells a t v holes,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    exists al, live_allocation m a = AccessOk al.
  Proof.
    intros m cells a t v holes H Ha.
    destruct (holds_allocation m cells a t v holes H Ha) as [l [bs [_ [_ [_ [_ Hm]]]]]].
    unfold live_allocation. rewrite Hm. simpl. eexists. reflexivity.
  Qed.

  Lemma live_allocation_fresh : forall m cells a t,
    models m cells -> nth_error cells a = Some (Fresh t) ->
    exists al, live_allocation m a = AccessOk al.
  Proof.
    intros m cells a t H Ha. destruct (models_nth m cells a _ H Ha) as [al [Hal [l [_ ->]]]].
    unfold live_allocation. rewrite Hal. simpl. eexists. reflexivity.
  Qed.

  Lemma mod_of_divide : forall a b, Nat.divide a b -> Nat.eqb (b mod a) 0 = true.
  Proof. intros a b H. apply Nat.eqb_eq. apply Nat.Lcm0.mod_divide. exact H. Qed.

  Lemma load_value_holds : forall m cells a t v holes l p o lt vt ty meta variant,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l -> at_path l v p = Some (o, lt, vt) -> layout_of adts ty = Some lt ->
    apart_from_holes l v holes o (size_of lt) ->
    references_valid adts m lt vt = AccessOk tt ->
    load_value adts m (Location a o ty meta variant) = AccessOk vt.
  Proof.
    intros m cells a t v holes l p o lt vt ty meta variant H Ha Hl Hp Hty Hholes Hrefs.
    destruct (holds_allocation m cells a t v holes H Ha) as [l' [bs [Hl' [Hbs [Hvt [Hwf Hm]]]]]].
    rewrite Hl in Hl'. injection Hl' as <-.
    destruct (at_path_encode p l v o lt vt bs Hwf Hbs Hp) as [Hwft [Hfit [Hda [Hdo Henc]]]].
    unfold load_value, located_layout. simpl. rewrite Hty. simpl.
    unfold load, live_allocation. rewrite Hm. simpl.
    unfold check_range. simpl.
    rewrite (proj2 (Nat.leb_le _ _) Hfit), mod_of_divide, mod_of_divide by assumption. simpl.
    rewrite bytes_at_punch by assumption.
    rewrite (decode_encode lt vt _ Hwft (at_path_vtable_free p l v o lt vt Hp Hvt) Henc).
    simpl. rewrite Hrefs. reflexivity.
  Qed.

  Lemma nth_error_lt : forall (A : Type) (xs : list A) a x, nth_error xs a = Some x -> a < length xs.
  Proof. intros A xs a x H. apply nth_error_Some. congruence. Qed.

  Lemma set_nth_exists : forall (A : Type) (xs : list A) a x,
    a < length xs -> exists ys, set_nth a x xs = Some ys.
  Proof. intros A xs a x H. destruct (set_nth_some A xs a x H) as [ys [E _]]. exists ys. exact E. Qed.

  Lemma store_value_holds : forall m cells a t v l p o lt vt ty meta variant x bx,
    models m cells -> nth_error cells a = Some (Holds t v []) ->
    layout_of adts t = Some l -> at_path l v p = Some (o, lt, vt) -> layout_of adts ty = Some lt ->
    encode lt x = Some bx -> vtable_free x = true ->
    references_valid adts m lt x = AccessOk tt ->
    exists v2 m' cells', set_path l v p x = Some v2
      /\ set_nth a (Holds t v2 []) cells = Some cells'
      /\ store_value adts m (Location a o ty meta variant) x = AccessOk m' /\ models m' cells'.
  Proof.
    intros m cells a t v l p o lt vt ty meta variant x bx H Ha Hl Hp Hty Hx Hvx Hrefs.
    destruct (holds_allocation m cells a t v [] H Ha) as [l' [bs [Hl' [Hbs [Hvt [Hwf Hm]]]]]].
    rewrite Hl in Hl'. injection Hl' as <-. simpl in Hm.
    destruct (at_path_encode p l v o lt vt bs Hwf Hbs Hp) as [Hwft [Hfit [Hda [Hdo _]]]].
    destruct (set_path_encode p l v o lt vt x bs bx Hwf Hbs Hp Hx) as [v2 [Hset Henc2]].
    assert (Hlen : length bx = size_of lt) by exact (encode_length lt x bx Hwft Hx).
    destruct (set_nth_exists _ m a
                (AllocationData (size_of l) (align_of l) (splice o bx bs) true)
                (nth_error_lt _ _ _ _ Hm)) as [m' Hm'].
    destruct (models_set m cells a (Holds t v2 []) (AllocationData (size_of l) (align_of l) (splice o bx bs) true) m' H (nth_error_lt _ _ _ _ Ha)) as
      [cells' [Hc' Hmod]]; [| exact Hm' |].
    { exists l, (splice o bx bs). repeat split; try assumption.
      eapply set_path_vtable_free; eassumption. }
    exists v2, m', cells'. split; [exact Hset|]. split; [exact Hc'|]. split; [|exact Hmod].
    unfold store_value, located_layout. simpl. rewrite Hty. simpl. rewrite Hx. simpl.
    rewrite Hrefs. simpl. unfold store, live_allocation. rewrite Hm. simpl.
    unfold check_range. simpl. rewrite Hlen.
    rewrite (proj2 (Nat.leb_le _ _) Hfit), mod_of_divide, mod_of_divide by assumption. simpl.
    unfold with_bytes. simpl. rewrite Hm'. reflexivity.
  Qed.

  Definition cell_type (c : cell) : option ty :=
    match c with
    | Holds t _ _ | Fresh t => Some t
    | _ => None
    end.

  Lemma typed_allocation : forall m cells a c t l,
    models m cells -> nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    exists bytes, nth_error m a = Some (AllocationData (size_of l) (align_of l) bytes true)
      /\ length bytes = size_of l.
  Proof.
    intros m cells a c t l H Ha Hc Hl.
    destruct (models_nth m cells a c H Ha) as [al [Hal Hmod]].
    destruct c as [t' v holes | t' | | ]; simpl in Hc; try discriminate; injection Hc as ->.
    - destruct Hmod as [l' [bs [Hl' [Hbs [_ ->]]]]]. rewrite Hl in Hl'. injection Hl' as <-.
      exists (punch l v holes bs). split; [exact Hal|].
      pose proof (layout_of_wf adts t l Hl) as Hwf.
      rewrite length_punch by assumption. exact (encode_length l v bs Hwf Hbs).
    - destruct Hmod as [l' [Hl' ->]]. rewrite Hl in Hl'. injection Hl' as <-.
      exists (repeat MUninit (size_of l)). split; [exact Hal | apply repeat_length].
  Qed.

  Lemma store_value_whole : forall m cells a c t l ty meta variant x bx,
    models m cells -> nth_error cells a = Some c -> cell_type c = Some t ->
    layout_of adts t = Some l -> layout_of adts ty = Some l ->
    encode l x = Some bx -> vtable_free x = true -> references_valid adts m l x = AccessOk tt ->
    exists m' cells', set_nth a (Holds t x []) cells = Some cells'
      /\ store_value adts m (Location a 0 ty meta variant) x = AccessOk m' /\ models m' cells'.
  Proof.
    intros m cells a c t l ty meta variant x bx H Ha Hc Hl Hty Hx Hvx Hrefs.
    destruct (typed_allocation m cells a c t l H Ha Hc Hl) as [bytes [Hm Hlen]].
    pose proof (layout_of_wf adts t l Hl) as Hwf.
    assert (Hbx : length bx = size_of l) by exact (encode_length l x bx Hwf Hx).
    destruct (wf_basic l Hwf) as [Ha1 _].
    destruct (set_nth_exists _ m a (AllocationData (size_of l) (align_of l) bx true)
                (nth_error_lt _ _ _ _ Hm)) as [m' Hm'].
    destruct (models_set m cells a (Holds t x []) (AllocationData (size_of l) (align_of l) bx true) m' H (nth_error_lt _ _ _ _ Ha)) as
      [cells' [Hc' Hmod]]; [| exact Hm' |].
    { exists l, bx. repeat split; assumption. }
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hmod].
    unfold store_value, located_layout. simpl. rewrite Hty. simpl. rewrite Hx. simpl.
    rewrite Hrefs. simpl. unfold store, live_allocation. rewrite Hm. simpl.
    unfold check_range. simpl. rewrite Hbx, Nat.leb_refl, Nat.Div0.mod_same, Nat.Div0.mod_0_l.
    simpl. unfold with_bytes. simpl. rewrite splice_whole by lia. rewrite Hm'. reflexivity.
  Qed.

  Lemma deinit_whole : forall m cells a c t l,
    models m cells -> nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    exists m' cells', set_nth a (Fresh t) cells = Some cells'
      /\ store m a 0 (repeat MUninit (size_of l)) 1 = AccessOk m' /\ models m' cells'.
  Proof.
    intros m cells a c t l H Ha Hc Hl.
    destruct (typed_allocation m cells a c t l H Ha Hc Hl) as [bytes [Hm Hlen]].
    destruct (set_nth_exists _ m a
                (AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) true)
                (nth_error_lt _ _ _ _ Hm)) as [m' Hm'].
    destruct (models_set m cells a (Fresh t) (AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) true) m' H (nth_error_lt _ _ _ _ Ha)) as
      [cells' [Hc' Hmod]]; [| exact Hm' |].
    { exists l. split; [exact Hl | reflexivity]. }
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hmod].
    unfold store, live_allocation. rewrite Hm. simpl. unfold check_range. simpl.
    rewrite repeat_length, Nat.leb_refl. simpl.
    unfold with_bytes. simpl.
    rewrite splice_whole by (rewrite repeat_length; lia). rewrite Hm'. reflexivity.
  Qed.

  Lemma deinit_path : forall m cells a t v holes l p o lt vt,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l -> at_path l v p = Some (o, lt, vt) ->
    exists m' cells', set_nth a (Holds t v (p :: holes)) cells = Some cells'
      /\ store m a o (repeat MUninit (size_of lt)) 1 = AccessOk m' /\ models m' cells'.
  Proof.
    intros m cells a t v holes l p o lt vt H Ha Hl Hp.
    destruct (holds_allocation m cells a t v holes H Ha) as [l' [bs [Hl' [Hbs [Hvt [Hwf Hm]]]]]].
    rewrite Hl in Hl'. injection Hl' as <-.
    destruct (at_path_encode p l v o lt vt bs Hwf Hbs Hp) as [_ [Hfit _]].
    destruct (set_nth_exists _ m a
                (AllocationData (size_of l) (align_of l)
                   (splice o (repeat MUninit (size_of lt)) (punch l v holes bs)) true)
                (nth_error_lt _ _ _ _ Hm)) as [m' Hm'].
    destruct (models_set m cells a (Holds t v (p :: holes)) (AllocationData (size_of l) (align_of l)
                   (splice o (repeat MUninit (size_of lt)) (punch l v holes bs)) true) m' H (nth_error_lt _ _ _ _ Ha)) as
      [cells' [Hc' Hmod]]; [| exact Hm' |].
    { exists l, bs. repeat split; try assumption. simpl. rewrite Hp. reflexivity. }
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hmod].
    unfold store, live_allocation. rewrite Hm. unfold check_range.
    cbn [allocation_size allocation_align allocation_bytes allocation_live and_then].
    rewrite repeat_length, (proj2 (Nat.leb_le _ _) Hfit), !Nat.mod_1_r. simpl.
    unfold with_bytes. simpl. rewrite Hm'. reflexivity.
  Qed.

  Lemma enum_tag_bytes : forall d size align tag_offset tag_size variants k vs bs,
    layout_wf (LEnum d size align tag_offset tag_size variants) ->
    encode (LEnum d size align tag_offset tag_size variants) (VAdt d k vs) = Some bs ->
    bytes_at tag_offset tag_size bs = int_bytes tag_size (Z.of_nat k) None
    /\ (Z.of_nat k < 256 ^ Z.of_nat tag_size)%Z.
  Proof.
    intros d size align tag_offset tag_size variants k vs bs Hwf H.
    cbn [encode] in H. rewrite String.eqb_refl, nth_error_map in H.
    destruct (nth_error variants k) as [variant|] eqn:Hk; [|discriminate]. cbn [option_map] in H.
    destruct (encode variant (VTuple vs)) as [vb|] eqn:Hvb; [|discriminate].
    injection H as <-.
    pose proof (enum_variants_wf _ _ _ _ _ _ Hwf) as Hvw.
    destruct (variant_of_enum _ _ _ _ _ _ _ _ Hwf Hk) as [fields [-> [Hvwf _]]].
    destruct Hwf as [[_ [_ [_ [Htag [Hroom _]]]]] _].
    assert (Hkl : k < length variants) by (apply nth_error_Some; congruence).
    assert (Hvlen : length vb = size) by (rewrite (encode_length _ _ _ Hvwf Hvb); reflexivity).
    split; [|lia].
    apply bytes_at_splice_length; [apply length_int_bytes | lia].
  Qed.

  Lemma variant_tag_holds : forall m cells a t v holes l p o d size align tag_offset tag_size
      variants k vs ty meta variant,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l ->
    at_path l v p = Some (o, LEnum d size align tag_offset tag_size variants, VAdt d k vs) ->
    layout_of adts ty = Some (LEnum d size align tag_offset tag_size variants) ->
    apart_from_holes l v holes o size ->
    variant_tag adts m (Location a o ty meta variant) = AccessOk (Some k).
  Proof.
    intros m cells a t v holes l p o d size align tag_offset tag_size variants k vs ty meta variant
      H Ha Hl Hp Hty Hholes.
    destruct (holds_allocation m cells a t v holes H Ha) as [l' [bs [Hl' [Hbs [Hvt [Hwf Hm]]]]]].
    rewrite Hl in Hl'. injection Hl' as <-.
    destruct (at_path_encode p l v o _ _ bs Hwf Hbs Hp) as [Hwft [Hfit [_ [_ Henc]]]].
    destruct (enum_tag_bytes _ _ _ _ _ _ _ _ _ Hwft Henc) as [Htag Hroom].
    pose proof Hwft as Hwft'. destruct Hwft' as [[_ [_ [_ [Htagfit _]]]] _]. simpl in Hfit.
    unfold variant_tag, located_layout. simpl. rewrite Hty. simpl.
    unfold load, live_allocation. rewrite Hm. unfold check_range.
    cbn [allocation_size allocation_align allocation_bytes allocation_live and_then].
    rewrite (proj2 (Nat.leb_le (o + tag_offset + tag_size) (size_of l)) ltac:(lia)),
      !Nat.mod_1_r. simpl.
    rewrite (bytes_at_punch l v holes bs (o + tag_offset) tag_size); [|assumption|assumption|].
    - simpl in Htag. rewrite <- (bytes_at_bytes_at tag_offset tag_size o size) by lia.
      rewrite Htag, int_value_int_bytes by lia. simpl. rewrite Nat2Z.id. reflexivity.
    - eapply Forall_impl; [|exact Hholes]. intros q Hq. cbv beta in Hq |- *. revert Hq.
      destruct (at_path l v q) as [[[oq lq] vq]|]; [|intros; exact I].
      intros Hq. unfold apart in *. lia.
  Qed.

  Lemma valid_reference_holds : forall m cells a t v holes l p o lt vt pointee,
    models m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l -> at_path l v p = Some (o, lt, vt) ->
    extent adts pointee PointerThin = Some (size_of lt, align_of lt) ->
    valid_reference adts m pointee (PointerValue (ProvenanceAllocation a) (Z.of_nat o) PointerThin)
    = AccessOk tt.
  Proof.
    intros m cells a t v holes l p o lt vt pointee H Ha Hl Hp He.
    destruct (holds_allocation m cells a t v holes H Ha) as [l' [bs [Hl' [Hbs [Hvt [Hwf Hm]]]]]].
    rewrite Hl in Hl'. injection Hl' as <-.
    destruct (at_path_encode p l v o lt vt bs Hwf Hbs Hp) as [Hwft [Hfit [Hda [Hdo _]]]].
    unfold valid_reference. simpl. rewrite He.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat o)) ltac:(lia)). simpl. rewrite Nat2Z.id.
    destruct (Nat.eqb (size_of lt) 0).
    - simpl. rewrite mod_of_divide by assumption. reflexivity.
    - unfold live_allocation. rewrite Hm. simpl. unfold check_range. simpl.
      rewrite (proj2 (Nat.leb_le _ _) Hfit), mod_of_divide, mod_of_divide by assumption.
      reflexivity.
  Qed.

  Lemma valid_reference_whole : forall m cells a c t l pointee,
    models m cells -> nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    extent adts pointee PointerThin = Some (size_of l, align_of l) ->
    valid_reference adts m pointee (PointerValue (ProvenanceAllocation a) 0 PointerThin) = AccessOk tt.
  Proof.
    intros m cells a c t l pointee H Ha Hc Hl He.
    destruct (typed_allocation m cells a c t l H Ha Hc Hl) as [bytes [Hm Hlen]].
    unfold valid_reference. simpl. rewrite He. simpl.
    destruct (Nat.eqb (size_of l) 0).
    - simpl. rewrite Nat.Div0.mod_0_l. reflexivity.
    - unfold live_allocation. rewrite Hm. simpl. unfold check_range. simpl.
      rewrite Nat.leb_refl, Nat.Div0.mod_same, Nat.Div0.mod_0_l. reflexivity.
  Qed.

  Lemma storage_live_fresh : forall local_tys locals m cells x t l locals',
    models m cells -> nth_error local_tys x = Some t -> layout_of adts t = Some l ->
    (forall a, nth_error locals x <> Some (LocalAllocated a)) ->
    set_nth x (LocalAllocated (length cells)) locals = Some locals' ->
    exists m', storage_live adts local_tys (ByteState locals m) x = Some (ByteState locals' m')
      /\ models m' (cells ++ [Fresh t]).
  Proof.
    intros local_tys locals m cells x t l locals' H Ht Hl Hnot Hs.
    exists (m ++ [AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) true]).
    split.
    - unfold storage_live, release_local. simpl. rewrite Ht.
      destruct (nth_error locals x) as [[| |a]|] eqn:E;
        [ | | exfalso; exact (Hnot a eq_refl) | ];
        unfold allocate_uninit, allocate; rewrite Hl; simpl;
        rewrite (models_length m cells H), Hs; reflexivity.
    - apply models_app; [exact H|]. exists l. split; [exact Hl | reflexivity].
  Qed.

  Lemma storage_dead_typed : forall m cells locals x a c t l locals',
    models m cells -> nth_error locals x = Some (LocalAllocated a) ->
    nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    set_nth x LocalDead locals = Some locals' ->
    exists m' cells', storage_dead (ByteState locals m) x = Some (ByteState locals' m')
      /\ set_nth a (Freed t) cells = Some cells' /\ models m' cells'.
  Proof.
    intros m cells locals x a c t l locals' H Hx Ha Hc Hl Hs.
    destruct (typed_allocation m cells a c t l H Ha Hc Hl) as [bytes [Hm Hlen]].
    destruct (set_nth_exists _ m a
                (AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) false)
                (nth_error_lt _ _ _ _ Hm)) as [m' Hm'].
    destruct (models_set m cells a (Freed t) (AllocationData (size_of l) (align_of l) (repeat MUninit (size_of l)) false) m' H (nth_error_lt _ _ _ _ Ha)) as
      [cells' [Hc' Hmod]]; [| exact Hm' |].
    { exists l. split; [exact Hl | reflexivity]. }
    exists m', cells'. split; [|split; assumption].
    unfold storage_dead, release_local, kill_allocation. simpl. rewrite Hs, Hx, Hm. simpl.
    rewrite Hm'. reflexivity.
  Qed.

  Lemma allocate_value_holds : forall m cells t v l bs,
    models m cells -> layout_of adts t = Some l -> encode l v = Some bs -> vtable_free v = true ->
    allocate_value adts m t v = Some (length cells, m ++ [AllocationData (size_of l) (align_of l) bs true])
    /\ models (m ++ [AllocationData (size_of l) (align_of l) bs true]) (cells ++ [Holds t v []]).
  Proof.
    intros m cells t v l bs H Hl Hbs Hvt. split.
    - unfold allocate_value, allocate. rewrite Hl, Hbs. simpl.
      rewrite (models_length m cells H). reflexivity.
    - apply models_app; [exact H|]. exists l, bs. repeat split; assumption.
  Qed.

End Models.

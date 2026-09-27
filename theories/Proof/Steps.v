From RustRocq Require Import Syntax Subst LayoutAlg Memory Denote.
From RustRocq Require Import Proof.Bytes Proof.Encoding Proof.Cells.
From Stdlib Require Import Bool List String ZArith Lia.
Import ListNotations.

Notation length := List.length.

Local Open Scope list_scope.

Section Wp.

  Definition wp {A} (m : M A) (st : prog_state) (Q : A -> prog_state -> Prop) : Prop :=
    match m st with
    | Ok a st' => Q a st'
    | _ => False
    end.

  Lemma wp_ret : forall A (a : A) st (Q : A -> prog_state -> Prop), Q a st -> wp (ret a) st Q.
  Proof. intros. exact H. Qed.

  Lemma wp_bind : forall A B (m : M A) (k : A -> M B) st Q,
    wp m st (fun a st' => wp (k a) st' Q) -> wp (bind m k) st Q.
  Proof.
    intros A B m k st Q H. unfold wp, bind in *. destruct (m st); try contradiction. exact H.
  Qed.

  Lemma wp_mono : forall A (m : M A) st (Q Q' : A -> prog_state -> Prop),
    wp m st Q -> (forall a st', Q a st' -> Q' a st') -> wp m st Q'.
  Proof. intros A m st Q Q' H Himp. unfold wp in *. destruct (m st); auto. Qed.

  Lemma wp_observe : forall A what (f : prog_state -> access_result A) st a Q,
    f st = AccessOk a -> Q a st -> wp (observe what f) st Q.
  Proof. intros A what f st a Q Hf HQ. unfold wp, observe, of_access. rewrite Hf. exact HQ. Qed.

  Lemma wp_change : forall what f st st' Q,
    f st = AccessOk st' -> Q tt st' -> wp (change what f) st Q.
  Proof. intros what f st st' Q Hf HQ. unfold wp, change. rewrite Hf. exact HQ. Qed.

  Lemma wp_of_option : forall A what (o : option A) a st Q,
    o = Some a -> Q a st -> wp (of_option what o) st Q.
  Proof. intros A what o a st Q -> HQ. exact HQ. Qed.

End Wp.

Section Running.

  Context `{Alg : LayoutAlg}.

  Definition finishes (P : program) (n : nat) (b : body) (l : block_id) (st : prog_state)
      (Q : outcome result -> Prop) : Prop :=
    match run_block P n b l st with
    | Some o => Q o
    | None => False
    end.

  Definition returns_into (P : program) (n : nat) (b : body) (dest : place) (target : option block_id)
      (saved : list local_storage) (Q : outcome result -> Prop) (o : outcome result) : Prop :=
    match o with
    | Ok (Returned v) st =>
        wp (return_to P b dest target v) (state_with_locals st saved)
          (fun t st' => finishes P n b t st' Q)
    | Ok r st => Q (Ok r (state_with_locals st saved))
    | _ => False
    end.

  Lemma finishes_step : forall P n b l st Q,
    wp (denote_block P b l) st (fun c st' =>
      match c with
      | Goto l' => finishes P n b l' st' Q
      | Finish r => Q (Ok r st')
      | Enter callee saved dest target =>
          finishes P n callee 0 st' (returns_into P n b dest target saved Q)
      | Model g gargs vs dest target =>
          match pg_ext P (callback_with P (fun callee => run_block P n callee 0))
                  (pg_adts P) g gargs vs st' with
          | Some o => returns_into P n b dest target (state_locals st') Q o
          | None => False
          end
      end) ->
    finishes P (S n) b l st Q.
  Proof.
    intros P n b l st Q H. unfold finishes, wp in *. cbn [run_block].
    destruct (denote_block P b l st) as [c st'| | |]; try contradiction.
    destruct c as [l'|r|callee saved dest target|g gargs vs dest target].
    - exact H.
    - exact H.
    - unfold after_call. destruct (run_block P n callee 0 st') as [o|]; [|contradiction].
      unfold returns_into in H.
      destruct o as [[v| |] st''| | |]; try contradiction; try exact H.
      unfold wp in H. destruct (return_to P b dest target v _) as [t st3| | |]; try contradiction.
      exact H.
    - unfold after_call. destruct (pg_ext P _ _ g gargs vs st') as [o|]; [|contradiction].
      unfold returns_into in H.
      destruct o as [[v| |] st''| | |]; try contradiction; try exact H.
      unfold wp in H. destruct (return_to P b dest target v _) as [t st3| | |]; try contradiction.
      exact H.
  Qed.

  Lemma finishes_mono : forall P n b l st (Q Q' : outcome result -> Prop),
    finishes P n b l st Q -> (forall o, Q o -> Q' o) -> finishes P n b l st Q'.
  Proof.
    intros P n b l st Q Q' H Himp. unfold finishes in *.
    destruct (run_block P n b l st); [apply Himp; exact H | contradiction].
  Qed.

  Lemma finishes_more : forall P n m b l st Q,
    n <= m -> finishes P n b l st Q -> finishes P m b l st Q.
  Proof.
    intros P n m b l st Q Hle H. unfold finishes in *.
    destruct (run_block P n b l st) as [o|] eqn:E; [|contradiction].
    rewrite (run_block_monotone P n m b l st o Hle E). exact H.
  Qed.

End Running.

Section Primitives.

  Context `{Alg : LayoutAlg} (P : program) (b : body).

  Lemma wp_read : forall p st v Q,
    read_place (pg_adts P) (frame_tys b) st p = AccessOk v -> Q v st -> wp (read P b p) st Q.
  Proof. intros p st v Q H HQ. unfold read. eapply wp_observe; eassumption. Qed.

  Lemma wp_write : forall p v st st' Q,
    write_place (pg_adts P) (frame_tys b) st p v = AccessOk st' -> Q tt st' ->
    wp (write P b p v) st Q.
  Proof. intros p v st st' Q H HQ. unfold write. eapply wp_change; eassumption. Qed.

  Lemma wp_deinit : forall p st st' Q,
    deinit_place (pg_adts P) (frame_tys b) st p = AccessOk st' -> Q tt st' ->
    wp (deinit P b p) st Q.
  Proof. intros p st st' Q H HQ. unfold deinit. eapply wp_change; eassumption. Qed.

  Lemma wp_address_of : forall p st v Q,
    address_of_place (pg_adts P) (frame_tys b) st p = AccessOk v -> Q v st ->
    wp (address_of P b p) st Q.
  Proof. intros p st v Q H HQ. unfold address_of. eapply wp_observe; eassumption. Qed.

End Primitives.

Section Places.

  Context `{Alg : LayoutAlg} (adts : list adt_def) (tys : list ty).

  Lemma read_place_at : forall st p loc v,
    locate adts tys st p = AccessOk loc -> load_value adts (state_memory st) loc = AccessOk v ->
    read_place adts tys st p = AccessOk v.
  Proof. intros st p loc v Hl Hv. unfold read_place. rewrite Hl. exact Hv. Qed.

  Lemma write_place_at : forall st p loc v m',
    locate adts tys st p = AccessOk loc -> store_value adts (state_memory st) loc v = AccessOk m' ->
    write_place adts tys st p v = AccessOk (state_with_memory st m').
  Proof. intros st p loc v m' Hl Hv. unfold write_place. rewrite Hl. simpl. rewrite Hv. reflexivity. Qed.

  Lemma address_of_place_at : forall st p loc,
    locate adts tys st p = AccessOk loc ->
    address_of_place adts tys st p =
      AccessOk (VPtr (PointerValue (ProvenanceAllocation (loc_allocation loc))
                        (Z.of_nat (loc_offset loc)) (loc_metadata loc))).
  Proof. intros st p loc Hl. unfold address_of_place. rewrite Hl. reflexivity. Qed.

  Lemma deinit_place_at : forall st p loc size align m',
    locate adts tys st p = AccessOk loc ->
    extent adts (loc_ty loc) (loc_metadata loc) = Some (size, align) ->
    store (state_memory st) (loc_allocation loc) (loc_offset loc) (repeat MUninit size) 1
      = AccessOk m' ->
    deinit_place adts tys st p = AccessOk (state_with_memory st m').
  Proof.
    intros st p loc size align m' Hl He Hs. unfold deinit_place, located_extent.
    rewrite Hl. simpl. rewrite He. simpl. rewrite Hs. reflexivity.
  Qed.

  Lemma extent_thin : forall t l,
    unsized_view adts t = t -> (match t with TSlice _ | TStr | TDynamic _ _ => False | _ => True end) ->
    layout_of adts t = Some l -> extent adts t PointerThin = Some (size_of l, align_of l).
  Proof.
    intros t l Hv Ht Hl. unfold extent. rewrite Hv.
    destruct t; try contradiction; rewrite Hl; reflexivity.
  Qed.

End Places.

Section CellLists.

  Lemma nth_error_app_length : forall (A : Type) (xs ys : list A) k,
    nth_error (xs ++ ys) (length xs + k) = nth_error ys k.
  Proof. intros A xs ys k. rewrite nth_error_app2 by lia. f_equal. lia. Qed.

  Lemma nth_error_app_exact : forall (A : Type) (xs ys : list A),
    nth_error (xs ++ ys) (length xs) = nth_error ys 0.
  Proof. intros A xs ys. rewrite <- (Nat.add_0_r (length xs)). apply nth_error_app_length. Qed.

  Lemma set_nth_app_length : forall (A : Type) (xs ys : list A) k x,
    set_nth (length xs + k) x (xs ++ ys) = option_map (app xs) (set_nth k x ys).
  Proof.
    intros A xs ys k x. induction xs as [|y xs IH]; simpl; [destruct (set_nth k x ys); reflexivity|].
    rewrite IH. destruct (set_nth k x ys); reflexivity.
  Qed.

  Lemma set_nth_app_left : forall (A : Type) (xs ys : list A) i x,
    i < length xs -> set_nth i x (xs ++ ys) = option_map (fun xs' => xs' ++ ys) (set_nth i x xs).
  Proof.
    intros A xs ys i x. revert i. induction xs as [|y xs IH]; intros i Hi; simpl in *; [lia|].
    destruct i as [|i]; [reflexivity|]. simpl. rewrite IH by lia. destruct (set_nth i x xs); reflexivity.
  Qed.

End CellLists.

Section Locals.

  Context `{Alg : LayoutAlg} (adts : list adt_def) (tys : list ty).

  Lemma locate_local : forall locals m cells x a c t,
    models adts m cells -> nth_error locals x = Some (LocalAllocated a) -> nth_error tys x = Some t ->
    nth_error cells a = Some c -> (exists al, live_allocation m a = AccessOk al) ->
    locate adts tys (ByteState locals m) (Place x []) = AccessOk (Location a 0 t PointerThin None).
  Proof.
    intros locals m cells x a c t H Hx Ht Ha [al Hal].
    unfold locate, local_location. simpl. rewrite Hx, Ht, Hal. reflexivity.
  Qed.

  Lemma live_typed : forall m cells a c t,
    models adts m cells -> nth_error cells a = Some c -> cell_type c = Some t ->
    exists al, live_allocation m a = AccessOk al.
  Proof.
    intros m cells a c t H Ha Hc.
    destruct c; simpl in Hc; try discriminate.
    - eapply live_allocation_holds; eassumption.
    - eapply live_allocation_fresh; eassumption.
  Qed.

  Lemma storage_live_at : forall locals m cells x t l locals' n,
    models adts m cells -> nth_error tys x = Some t -> layout_of adts t = Some l ->
    (forall a, nth_error locals x <> Some (LocalAllocated a)) ->
    length cells = n -> set_nth x (LocalAllocated n) locals = Some locals' ->
    exists m', storage_live adts tys (ByteState locals m) x = Some (ByteState locals' m')
      /\ models adts m' (cells ++ [Fresh t]).
  Proof.
    intros locals m cells x t l locals' n H Ht Hl Hnot <- Hs.
    eapply storage_live_fresh; eassumption.
  Qed.

  Lemma write_local : forall locals m cells x a c t l v bx,
    models adts m cells -> nth_error locals x = Some (LocalAllocated a) -> nth_error tys x = Some t ->
    nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    encode l v = Some bx -> vtable_free v = true -> references_valid adts m l v = AccessOk tt ->
    exists m' cells', set_nth a (Holds t v []) cells = Some cells'
      /\ write_place adts tys (ByteState locals m) (Place x []) v = AccessOk (ByteState locals m')
      /\ models adts m' cells'.
  Proof.
    intros locals m cells x a c t l v bx H Hx Ht Ha Hc Hl Hv Hvt Hr.
    destruct (store_value_whole adts m cells a c t l t PointerThin None v bx H Ha Hc Hl Hl Hv Hvt Hr)
      as [m' [cells' [Hc' [Hs Hm']]]].
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hm'].
    erewrite write_place_at; [reflexivity | |].
    - eapply locate_local; try eassumption. eapply live_typed; eassumption.
    - exact Hs.
  Qed.

  Lemma read_local : forall locals m cells x a t v holes l,
    models adts m cells -> nth_error locals x = Some (LocalAllocated a) -> nth_error tys x = Some t ->
    nth_error cells a = Some (Holds t v holes) -> layout_of adts t = Some l ->
    apart_from_holes l v holes 0 (size_of l) -> references_valid adts m l v = AccessOk tt ->
    read_place adts tys (ByteState locals m) (Place x []) = AccessOk v.
  Proof.
    intros locals m cells x a t v holes l H Hx Ht Ha Hl Hholes Hr.
    eapply read_place_at.
    - eapply locate_local; try eassumption. eapply live_allocation_holds; eassumption.
    - eapply load_value_holds with (p := []); try eassumption. reflexivity.
  Qed.

  Lemma deinit_local : forall locals m cells x a c t l,
    models adts m cells -> nth_error locals x = Some (LocalAllocated a) -> nth_error tys x = Some t ->
    nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    extent adts t PointerThin = Some (size_of l, align_of l) ->
    exists m' cells', set_nth a (Fresh t) cells = Some cells'
      /\ deinit_place adts tys (ByteState locals m) (Place x []) = AccessOk (ByteState locals m')
      /\ models adts m' cells'.
  Proof.
    intros locals m cells x a c t l H Hx Ht Ha Hc Hl He.
    destruct (deinit_whole adts m cells a c t l H Ha Hc Hl) as [m' [cells' [Hc' [Hs Hm']]]].
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hm'].
    erewrite (deinit_place_at adts tys _ _ (Location a 0 t PointerThin None));
      [reflexivity | | exact He | exact Hs].
    eapply locate_local; try eassumption. eapply live_typed; eassumption.
  Qed.

  Lemma storage_dead_local : forall locals m cells x a c t l locals',
    models adts m cells -> nth_error locals x = Some (LocalAllocated a) ->
    nth_error cells a = Some c -> cell_type c = Some t -> layout_of adts t = Some l ->
    set_nth x LocalDead locals = Some locals' ->
    exists m' cells', storage_dead (ByteState locals m) x = Some (ByteState locals' m')
      /\ set_nth a (Freed t) cells = Some cells' /\ models adts m' cells'.
  Proof. intros. eapply storage_dead_typed; eassumption. Qed.

End Locals.

Section PlacePaths.

  Context `{Alg : LayoutAlg} (adts : list adt_def) (tys : list ty).

  Fixpoint path_of_projs (projs : list proj_elem) (acc : list step) : list step :=
    match projs with
    | [] => acc
    | PDeref :: rest => path_of_projs rest []
    | PField i _ :: rest => path_of_projs rest (acc ++ [Field i])
    | _ :: rest => path_of_projs rest acc
    end.

  Lemma read_place_path : forall st x projs m cells a off t meta var T V holes L p off' lt vt,
    state_memory st = m -> models adts m cells ->
    locate adts tys st (Place x projs) = AccessOk (Location a off t meta var) ->
    nth_error cells a = Some (Holds T V holes) -> layout_of adts T = Some L ->
    at_path L V p = Some (off', lt, vt) -> off = off' -> layout_of adts t = Some lt ->
    apart_from_holes L V holes off (size_of lt) -> references_valid adts m lt vt = AccessOk tt ->
    read_place adts tys st (Place x projs) = AccessOk vt.
  Proof.
    intros st x projs m cells a off t meta var T V holes L p off' lt vt Hst H Hloc Ha HL Hp -> Ht
      Hholes Hr.
    eapply read_place_at; [exact Hloc|]. rewrite Hst.
    eapply load_value_holds; eassumption.
  Qed.

  Lemma write_place_path : forall st x projs m cells a off t meta var T V L p off' lt vt v bx,
    state_memory st = m -> models adts m cells ->
    locate adts tys st (Place x projs) = AccessOk (Location a off t meta var) ->
    nth_error cells a = Some (Holds T V []) -> layout_of adts T = Some L ->
    at_path L V p = Some (off', lt, vt) -> off = off' -> layout_of adts t = Some lt ->
    encode lt v = Some bx -> vtable_free v = true -> references_valid adts m lt v = AccessOk tt ->
    exists V' m' cells', set_path L V p v = Some V'
      /\ set_nth a (Holds T V' []) cells = Some cells'
      /\ write_place adts tys st (Place x projs) v = AccessOk (state_with_memory st m')
      /\ models adts m' cells'.
  Proof.
    intros st x projs m cells a off t meta var T V L p off' lt vt v bx Hst H Hloc Ha HL Hp -> Ht
      Hv Hvt Hr.
    destruct (store_value_holds adts m cells a T V L p off' lt vt t meta var v bx H Ha HL Hp Ht Hv Hvt Hr)
      as [V' [m' [cells' [Hset [Hc' [Hs Hm']]]]]].
    exists V', m', cells'. split; [exact Hset|]. split; [exact Hc'|]. split; [|exact Hm'].
    eapply write_place_at; [exact Hloc|]. rewrite Hst. exact Hs.
  Qed.

  Lemma deinit_place_path : forall st x projs m cells a off t meta var T V holes L p off' lt vt,
    state_memory st = m -> models adts m cells ->
    locate adts tys st (Place x projs) = AccessOk (Location a off t meta var) ->
    nth_error cells a = Some (Holds T V holes) -> layout_of adts T = Some L ->
    at_path L V p = Some (off', lt, vt) -> off = off' ->
    extent adts t meta = Some (size_of lt, align_of lt) ->
    exists m' cells', set_nth a (Holds T V (p :: holes)) cells = Some cells'
      /\ deinit_place adts tys st (Place x projs) = AccessOk (state_with_memory st m')
      /\ models adts m' cells'.
  Proof.
    intros st x projs m cells a off t meta var T V holes L p off' lt vt Hst H Hloc Ha HL Hp -> He.
    destruct (deinit_path adts m cells a T V holes L p off' lt vt H Ha HL Hp)
      as [m' [cells' [Hc' [Hs Hm']]]].
    exists m', cells'. split; [exact Hc'|]. split; [|exact Hm'].
    eapply deinit_place_at; [exact Hloc | exact He |]. rewrite Hst. exact Hs.
  Qed.

End PlacePaths.

Section Candidates.

  Fixpoint field_paths (depth : nat) (v : runtime_value) : list (list step) :=
    match depth with
    | O => [[]]
    | S d =>
        [] :: match v with
              | VTuple vs | VAdt _ _ vs =>
                  List.concat (map (fun '(i, x) => map (cons (Field i)) (field_paths d x))
                              (combine (seq 0 (length vs)) vs))
              | _ => []
              end
    end.

End Candidates.

Section Models.

  Context `{Alg : LayoutAlg}.

  Lemma wp_model : forall P n b dest target saved Q cb g gargs vs st (m : M result),
    pg_ext P cb (pg_adts P) g gargs vs st = Some (m st) ->
    wp m st (fun r st' => returns_into P n b dest target saved Q (Ok r st')) ->
    match pg_ext P cb (pg_adts P) g gargs vs st with
    | Some o => returns_into P n b dest target saved Q o
    | None => False
    end.
  Proof.
    intros P n b dest target saved Q cb g gargs vs st m Hext H. rewrite Hext.
    unfold wp in H. destruct (m st) as [r st'| | |]; try contradiction. exact H.
  Qed.

  Lemma read_pointer_path : forall adts m cells a off t T V holes L p off' lt vt,
    models adts m cells -> nth_error cells a = Some (Holds T V holes) -> layout_of adts T = Some L ->
    at_path L V p = Some (off', lt, vt) -> off = off' -> layout_of adts t = Some lt ->
    apart_from_holes L V holes off (size_of lt) -> references_valid adts m lt vt = AccessOk tt ->
    read_pointer adts m t (PointerValue (ProvenanceAllocation a) (Z.of_nat off) PointerThin)
      = AccessOk vt.
  Proof.
    intros adts m cells a off t T V holes L p off' lt vt H Ha HL Hp -> Ht Hholes Hr.
    unfold read_pointer, pointer_target. simpl.
    rewrite (proj2 (Z.leb_le 0 (Z.of_nat off')) ltac:(lia)). simpl. rewrite Nat2Z.id.
    eapply load_value_holds; eassumption.
  Qed.

End Models.

Section MatchRules.

  Context `{Alg : LayoutAlg} (P : program) (b : body).

  Lemma wp_change_m : forall what f st Q,
    (match f st with AccessOk st' => Q tt st' | _ => False end) -> wp (change what f) st Q.
  Proof. intros what f st Q H. unfold wp, change. destruct (f st); tauto. Qed.

  Lemma wp_observe_m : forall A what (f : prog_state -> access_result A) st Q,
    (match f st with AccessOk a => Q a st | _ => False end) -> wp (observe what f) st Q.
  Proof. intros A what f st Q H. unfold wp, observe, of_access. destruct (f st); tauto. Qed.

  Lemma wp_read_m : forall p st Q,
    (match read_place (pg_adts P) (frame_tys b) st p with AccessOk v => Q v st | _ => False end) ->
    wp (read P b p) st Q.
  Proof. intros. unfold read. apply wp_observe_m. exact H. Qed.

  Lemma wp_write_m : forall p v st Q,
    (match write_place (pg_adts P) (frame_tys b) st p v with AccessOk st' => Q tt st' | _ => False end) ->
    wp (write P b p v) st Q.
  Proof. intros. unfold write. apply wp_change_m. exact H. Qed.

  Lemma wp_deinit_m : forall p st Q,
    (match deinit_place (pg_adts P) (frame_tys b) st p with AccessOk st' => Q tt st' | _ => False end) ->
    wp (deinit P b p) st Q.
  Proof. intros. unfold deinit. apply wp_change_m. exact H. Qed.

  Lemma wp_address_of_m : forall p st Q,
    (match address_of_place (pg_adts P) (frame_tys b) st p with AccessOk v => Q v st | _ => False end) ->
    wp (address_of P b p) st Q.
  Proof. intros. unfold address_of. apply wp_observe_m. exact H. Qed.

End MatchRules.

Section OffsetVariants.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Lemma valid_reference_at : forall m cells a t v holes l p off off' lt vt pointee,
    models adts m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l -> at_path l v p = Some (off', lt, vt) -> off = off' ->
    extent adts pointee PointerThin = Some (size_of lt, align_of lt) ->
    valid_reference adts m pointee (PointerValue (ProvenanceAllocation a) (Z.of_nat off) PointerThin)
    = AccessOk tt.
  Proof. intros. subst off. eapply valid_reference_holds; eassumption. Qed.

  Lemma load_value_at : forall m cells a t v holes l p off off' lt vt ty meta variant,
    models adts m cells -> nth_error cells a = Some (Holds t v holes) ->
    layout_of adts t = Some l -> at_path l v p = Some (off', lt, vt) -> off = off' ->
    layout_of adts ty = Some lt -> apart_from_holes l v holes off (size_of lt) ->
    references_valid adts m lt vt = AccessOk tt ->
    load_value adts m (Location a off ty meta variant) = AccessOk vt.
  Proof. intros. subst off. eapply load_value_holds; eassumption. Qed.

End OffsetVariants.

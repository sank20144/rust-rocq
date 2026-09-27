From RustRocq Require Import Syntax Subst LayoutAlg Memory Denote.
From RustRocq Require Import Proof.Bytes Proof.Encoding Proof.Cells Proof.Shapes Proof.Steps.
From Stdlib Require Import Bool List String ZArith Lia.
Import ListNotations.

Notation length := List.length.

Arguments bind : simpl never.
Arguments read : simpl never.
Arguments write : simpl never.
Arguments deinit : simpl never.
Arguments address_of : simpl never.
Arguments change : simpl never.
Arguments observe : simpl never.
Arguments layout_of : simpl never.
Arguments load_value : simpl never.
Arguments store_value : simpl never.
Arguments live_allocation : simpl never.
Arguments storage_live : simpl never.
Arguments storage_dead : simpl never.
Arguments read_place : simpl never.
Arguments write_place : simpl never.
Arguments deinit_place : simpl never.
Arguments address_of_place : simpl never.
Arguments encodable : simpl never.
Arguments references_valid : simpl never.
Arguments valid_reference : simpl never.
Arguments read_pointer : simpl never.
Arguments write_pointer : simpl never.
Arguments variant_tag : simpl never.
Arguments locate : simpl never.
Arguments allocate_value : simpl never.
Arguments finishes : simpl never.
Arguments run_block : simpl never.
Arguments returns_into : simpl never.
Arguments wp : simpl never.

Section Primitive.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Lemma layout_uint : forall w, layout_of adts (TUint w) = Some (LInt w).
  Proof. intros. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_int : forall w, layout_of adts (TInt w) = Some (LInt w).
  Proof. intros. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_bool : layout_of adts TBool = Some LBool.
  Proof. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_unit : layout_of adts (TTuple []) = Some LUnit.
  Proof. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_never : layout_of adts TNever = Some LNever.
  Proof. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_ref : forall r t mu,
    layout_of adts (TRef r t mu) = Some (LRef t (pointer_kind_to adts t)).
  Proof. intros. rewrite layout_of_eq. reflexivity. Qed.

  Lemma layout_raw : forall t mu,
    layout_of adts (TRawPtr t mu) = Some (LRawPtr (pointer_kind_to adts t)).
  Proof. intros. rewrite layout_of_eq. reflexivity. Qed.

  Lemma encodable_of : forall t l v bs,
    layout_of adts t = Some l -> encode l v = Some bs -> encodable adts t v = true.
  Proof. intros t l v bs Hl Hv. unfold encodable. rewrite Hl, Hv. reflexivity. Qed.

End Primitive.

Ltac z_facts :=
  repeat match goal with
  | |- context [(?a <=? ?b)%Z] =>
      first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [(?a <? ?b)%Z] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  | |- context [Z.eqb ?a ?b] =>
      first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  end.

Ltac lay :=
  first [ match goal with H : layout_of _ ?t = Some _ |- context [layout_of _ ?t] => rewrite H end
        | rewrite layout_uint | rewrite layout_int | rewrite layout_bool | rewrite layout_unit
        | rewrite layout_never | rewrite layout_ref | rewrite layout_raw ].

Ltac lay_eq := lay; cbn; reflexivity.

Ltac length_of cells :=
  lazymatch cells with
  | app ?c0 ?F => let k := eval cbn in (length F) in constr:(length c0 + k)
  | _ => constr:(length cells)
  end.

Ltac cells_norm H := rewrite <- ?app_assoc in H; cbn [app] in H.

Ltac cell_lookup :=
  first [ rewrite nth_error_app_length; reflexivity
        | rewrite nth_error_app_exact; reflexivity
        | rewrite nth_error_app1 by (apply nth_error_Some; congruence); eassumption
        | eassumption ].

Ltac find_models m := match goal with H : models _ m _ |- _ => H end.

Ltac normalize_state :=
  repeat match goal with
  | |- context [?f ?adts ?tys ?st] =>
      lazymatch f with
      | @storage_live _ => idtac | @write_place _ => idtac | @read_place _ => idtac
      | @deinit_place _ => idtac | @address_of_place _ => idtac | @locate _ => idtac
      end;
      lazymatch st with
      | ByteState _ _ => fail
      | context [storage_live _ _ _ _] => fail
      | context [write_place _ _ _ _ _] => fail
      | _ => let st' := eval cbv [state_with_locals state_with_memory state_memory state_locals] in st in
             progress change st with st'
      end
  | |- context [storage_dead ?st ?x] =>
      lazymatch st with
      | ByteState _ _ => fail
      | _ => let st' := eval cbv [state_with_locals state_with_memory state_memory state_locals] in st in
             progress change st with st'
      end
  end.

Ltac try_paths cands tac :=
  lazymatch cands with
  | nil => fail "no path matches"
  | cons ?p ?rest => first [ tac p | try_paths rest tac ]
  end.

Ltac solve_valid_reference :=
  match goal with
  | |- valid_reference ?adts ?m ?pointee (PointerValue (ProvenanceAllocation ?a) ?addr PointerThin)
       = AccessOk tt =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      first
        [ eapply (valid_reference_whole adts m cells a); [exact Hm | exact Hc | reflexivity | lay_eq |];
          apply extent_thin; [reflexivity | exact I | lay_eq]
        | lazymatch type of Hc with _ = Some (Holds ?T ?V ?holes) =>
          let Hl := fresh "Hl" in
          eassert (Hl : layout_of adts T = Some _) by lay_eq;
          lazymatch type of Hl with _ = Some ?L =>
          lazymatch addr with
          | Z.of_nat ?o_addr =>
              let cands := eval cbn in (field_paths 3 V) in
              try_paths cands ltac:(fun p =>
                let r := eval cbn in (at_path L V p) in
                lazymatch r with
                | Some (?o, ?lt, ?vt) =>
                    apply (valid_reference_at adts m cells a T V holes L p o_addr o lt vt pointee
                             Hm Hc Hl eq_refl);
                    [lia | apply extent_thin; [reflexivity | exact I | lay_eq]]
                end)
          end end end ]
      end
  end.

Ltac solve_refs :=
  unfold references_valid; cbn; repeat (rewrite_valid_reference || reflexivity)
with rewrite_valid_reference :=
  match goal with
  | |- context [valid_reference ?adts ?m ?pointee ?p] =>
      let H := fresh in
      assert (H : valid_reference adts m pointee p = AccessOk tt) by solve_valid_reference;
      rewrite H; clear H; cbn
  end.

Ltac do_storage_live :=
  normalize_state;
  match goal with
  | |- context [storage_live ?adts ?tys (ByteState ?locals ?m) ?x] =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let t := eval cbn in (nth_error tys x) in
      lazymatch t with Some ?t =>
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts t = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let n := length_of cells in
      let locals' := eval cbn in (set_nth x (LocalAllocated n) locals) in
      lazymatch locals' with Some ?locals' =>
      let m' := fresh "m" in let E := fresh "E" in let Hm' := fresh "Hm" in
      destruct (storage_live_at adts tys locals m cells x t l locals' n Hm eq_refl Hl
                  ltac:(intros ? ?; discriminate)
                  ltac:(rewrite ?length_app; reflexivity) eq_refl) as [m' [E Hm']];
      rewrite E; clear E Hm Hl; cells_norm Hm'
      end end end end
  end.

Ltac settle_cells H :=
  rewrite ?set_nth_app_length in H;
  first [ rewrite set_nth_app_left in H by (apply nth_error_Some; congruence) | idtac ];
  cbn in H; injection H as <-.

Ltac do_write_local :=
  normalize_state;
  match goal with
  | |- context [write_place ?adts ?tys (ByteState ?locals ?m) (Place ?x []) ?v] =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let la := eval cbn in (nth_error locals x) in
      lazymatch la with Some (LocalAllocated ?a) =>
      let t := eval cbn in (nth_error tys x) in
      lazymatch t with Some ?t =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts t = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let Hv := fresh "Hv" in
      assert (Hv : exists bx, encode l v = Some bx)
        by (eexists; cbn; try unfold encode_pointer, in_word_range; cbn; z_facts; reflexivity);
      let bx := fresh "bx" in destruct Hv as [bx Hv];
      let m' := fresh "m" in let cells' := fresh "cells" in let Hc' := fresh "Hc" in
      let E := fresh "E" in let Hm' := fresh "Hm" in
      destruct (write_local adts tys locals m cells x a _ t l v bx Hm eq_refl eq_refl Hc eq_refl Hl
                  Hv eq_refl ltac:(solve_refs))
        as [m' [cells' [Hc' [E Hm']]]];
      rewrite E; clear E Hm Hc Hv Hl; settle_cells Hc'
      end end end end
  end.

Ltac solve_apart := unfold apart_from_holes; cbn; repeat constructor.

Ltac do_read_local :=
  normalize_state;
  match goal with
  | |- context [read_place ?adts ?tys (ByteState ?locals ?m) (Place ?x [])] =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let la := eval cbn in (nth_error locals x) in
      lazymatch la with Some (LocalAllocated ?a) =>
      let t := eval cbn in (nth_error tys x) in
      lazymatch t with Some ?t =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      lazymatch type of Hc with _ = Some (Holds _ ?v ?holes) =>
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts t = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let E := fresh "E" in
      assert (E : read_place adts tys (ByteState locals m) (Place x []) = AccessOk v)
        by (apply (read_local adts tys locals m cells x a t v holes l Hm eq_refl eq_refl Hc Hl);
            [solve_apart | solve_refs]);
      rewrite E; clear E Hc Hl
      end end end end end
  end.

Ltac do_deinit_local :=
  normalize_state;
  match goal with
  | |- context [deinit_place ?adts ?tys (ByteState ?locals ?m) (Place ?x [])] =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let la := eval cbn in (nth_error locals x) in
      lazymatch la with Some (LocalAllocated ?a) =>
      let t := eval cbn in (nth_error tys x) in
      lazymatch t with Some ?t =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts t = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let m' := fresh "m" in let cells' := fresh "cells" in let Hc' := fresh "Hc" in
      let E := fresh "E" in let Hm' := fresh "Hm" in
      destruct (deinit_local adts tys locals m cells x a _ t l Hm eq_refl eq_refl Hc eq_refl Hl
                  ltac:(apply extent_thin; [reflexivity | exact I | exact Hl]))
        as [m' [cells' [Hc' [E Hm']]]];
      rewrite E; clear Hm Hc Hl; settle_cells Hc'
      end end end end
  end.

Ltac do_storage_dead :=
  normalize_state;
  match goal with
  | |- context [storage_dead (ByteState ?locals ?m) ?x] =>
      let Hm := find_models m in
      lazymatch type of Hm with models ?adts _ ?cells =>
      let la := eval cbn in (nth_error locals x) in
      lazymatch la with Some (LocalAllocated ?a) =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      lazymatch type of Hc with _ = Some ?c =>
      let t := eval cbn in (cell_type c) in
      lazymatch t with Some ?t =>
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts t = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let locals' := eval cbn in (set_nth x LocalDead locals) in
      lazymatch locals' with Some ?locals' =>
      let m' := fresh "m" in let cells' := fresh "cells" in let Hc' := fresh "Hc" in
      let E := fresh "E" in let Hm' := fresh "Hm" in
      destruct (storage_dead_local adts locals m cells x a c t l locals' Hm eq_refl Hc eq_refl Hl
                  eq_refl) as [m' [cells' [E [Hc' Hm']]]];
      rewrite E; clear Hm Hc Hl; settle_cells Hc'
      end end end end end end
  end.


Ltac solve_encodable :=
  repeat match goal with
  | |- context [encodable ?adts ?t ?v] =>
      let H := fresh in
      assert (H : encodable adts t v = true)
        by (unfold encodable; lay; cbn; z_facts; reflexivity);
      rewrite H; clear H
  end.

Ltac do_start_call :=
  unfold start_call; cbn; solve_encodable; cbn; apply wp_change_m; unfold enter_frame; cbn;
  repeat (do_storage_live; cbn); repeat (do_write_local; cbn).

Ltac rewrite_live :=
  match goal with
  | |- context [live_allocation ?m ?a] =>
      let Hm := find_models m in
      lazymatch type of Hm with models ?adts _ ?cells =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      lazymatch type of Hc with _ = Some ?c =>
      let al := fresh "al" in let Hal := fresh "Hal" in
      destruct (live_typed adts m cells a c _ Hm Hc eq_refl) as [al Hal];
      rewrite Hal; clear Hc Hal
      end end
  end.

Ltac rewrite_load_whole :=
  match goal with
  | |- context [load_value ?adts ?m (Location ?a 0 ?t ?meta ?var)] =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      lazymatch type of Hc with _ = Some (Holds ?T ?v ?holes) =>
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts T = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?l =>
      let Ht := fresh "Ht" in
      assert (Ht : layout_of adts t = Some l) by lay_eq;
      let E := fresh "E" in
      assert (E : load_value adts m (Location a 0 t meta var) = AccessOk v)
        by (apply (load_value_holds adts m cells a T v holes l [] 0 l v t meta var Hm Hc Hl eq_refl Ht);
            [solve_apart | solve_refs]);
      rewrite E; clear E Hc Hl Ht
      end end end
  end.

Ltac locate_loop :=
  repeat (cbn; try unfold located_layout; first [ rewrite_live | rewrite_load_whole | lay | reflexivity ]).

Ltac solve_locate := unfold locate, local_location; locate_loop.

Ltac do_address_of :=
  normalize_state;
  match goal with
  | |- context [address_of_place ?adts ?tys ?st ?p] =>
      let Hloc := fresh "Hloc" in
      eassert (Hloc : locate adts tys st p = AccessOk _) by solve_locate;
      rewrite (address_of_place_at adts tys st p _ Hloc); clear Hloc;
      cbv [inner loc_allocation loc_offset loc_metadata loc_ty loc_variant]
  end.

Ltac read_pointer_at :=
  match goal with
  | |- read_pointer ?adts ?m ?t (PointerValue (ProvenanceAllocation ?a) (Z.of_nat ?o_addr) PointerThin)
       = _ =>
      let Hm := find_models m in
      lazymatch type of Hm with models _ _ ?cells =>
      let Hc := fresh "Hc" in
      eassert (Hc : nth_error cells a = Some _) by cell_lookup;
      lazymatch type of Hc with _ = Some (Holds ?T ?V ?holes) =>
      let Hl := fresh "Hl" in
      eassert (Hl : layout_of adts T = Some _) by lay_eq;
      lazymatch type of Hl with _ = Some ?L =>
      let cands := eval cbn in (field_paths 3 V) in
      try_paths cands ltac:(fun p =>
        let r := eval cbn in (at_path L V p) in
        lazymatch r with
        | Some (?o, ?lt, ?vt) =>
            apply (read_pointer_path adts m cells a o_addr t T V holes L p o lt vt Hm Hc Hl eq_refl);
            [lia | lay_eq | solve_apart | solve_refs]
        end)
      end end end
  end.

Ltac do_read_pointer :=
  match goal with
  | |- context [read_pointer ?adts ?m ?t (PointerValue ?prov ?addr ?meta)] =>
      let addr' := lazymatch addr with Z0 => constr:(Z.of_nat 0) | _ => addr end in
      change (PointerValue prov addr meta) with (PointerValue prov addr' meta);
      let H := fresh in
      eassert (H : read_pointer adts m t (PointerValue prov addr' meta) = AccessOk _) by read_pointer_at;
      rewrite H; clear H; cbn
  end.

Ltac wp_step :=
  lazymatch goal with
  | |- wp (bind _ _) _ _ => apply wp_bind
  | |- wp (ret _) _ _ => apply wp_ret
  | |- wp (change _ _) _ _ =>
      apply wp_change_m; cbn;
      first [ do_storage_live | do_storage_dead | do_write_local | do_deinit_local ]
  | |- wp (read _ _ _) _ _ => apply wp_read_m; cbn; do_read_local
  | |- wp (write _ _ _ _) _ _ => apply wp_write_m; cbn; do_write_local
  | |- wp (deinit _ _ _) _ _ => apply wp_deinit_m; cbn; do_deinit_local
  | |- wp (address_of _ _ _) _ _ => apply wp_address_of_m; cbn; do_address_of
  | |- wp (observe _ _) _ _ => apply wp_observe_m; cbn; do_read_pointer
  end.

Ltac wp_run := repeat (cbn; wp_step).

Ltac wf_facts H :=
  let W := fresh "W" in
  pose proof (layout_of_wf _ _ _ H) as W;
  unfold layout_wf, struct_ok, enum_ok in W; fold layout_wf in W; cbn in W;
  repeat match goal with
  | W : _ /\ _ |- _ => let W1 := fresh "W" in destruct W as [W1 W]
  | W : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in W; cbn in W
  | W : Forall _ [] |- _ => clear W
  | W : True |- _ => clear W
  | W : Nat.divide _ _ |- _ => clear W
  | W : pairwise_apart _ |- _ => clear W
  | W : layout_wf _ |- _ => clear W
  | W : fold_right and True _ |- _ => clear W
  | W : Forall _ _ |- _ => clear W
  end.

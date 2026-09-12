From RustRocq Require Import Syntax Layout Memory Subst.
From Stdlib Require Import Bool List String ZArith Lia.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Open Scope list_scope.
Notation length := List.length.

Inductive repr :=
  | ReprRust
  | ReprC
  | ReprTransparent
  | ReprPacked.

Definition repr_of_name (n : name) : repr :=
  if String.eqb n "C" then ReprC
  else if String.eqb n "transparent" then ReprTransparent
  else if String.eqb n "packed" then ReprPacked
  else ReprRust.

Definition reprs_of (ns : list name) : list repr := map repr_of_name ns.

Inductive syn_type :=
  | StInt (w : int_width) (signed : bool)
  | StBool
  | StChar
  | StFloat (w : float_width)
  | StPtr (fat : bool)
  | StFnPtr
  | StUnit
  | StNever
  | StArray (elem : syn_type) (len : nat)
  | StTuple (fields : list syn_type)
  | StStruct (path : name) (fields : list syn_type) (r : list repr)
  | StEnum (path : name) (variants : list (list syn_type)) (r : list repr)
  | StUnion (path : name) (fields : list syn_type) (r : list repr)
  | StUnsized
  | StOpaque.

Definition find_adt (adts : list adt_def) (path : name) : option adt_def :=
  find (fun d => String.eqb (ad_path d) path) adts.

Definition unsized_ty (t : ty) : bool :=
  match t with
  | TSlice _ | TStr | TDynamic _ _ => true
  | _ => false
  end.

Definition variant_field_tys (args : list garg) (v : variant_def) : list ty :=
  map (fun f => subst_ty args (snd f)) (vd_fields v).

Fixpoint syn_type_of_fuel (fuel : nat) (adts : list adt_def) (t : ty) : syn_type :=
  match fuel with
  | O => StOpaque
  | S fuel =>
      let go := syn_type_of_fuel fuel adts in
      match t with
      | TBool => StBool
      | TChar => StChar
      | TInt w => StInt w true
      | TUint w => StInt w false
      | TFloat w => StFloat w
      | TRef _ p _ | TRawPtr p _ => StPtr (unsized_ty p)
      | TFnPtr _ => StFnPtr
      | TFnDef _ _ => StUnit
      | TNever => StNever
      | TTuple [] => StUnit
      | TTuple ts => StTuple (map go ts)
      | TArray e n =>
          match const_nat n with
          | Some k => StArray (go e) k
          | None => StOpaque
          end
      | TSlice _ | TStr | TDynamic _ _ => StUnsized
      | TClosure _ args =>
          match closure_upvars args with
          | Some u => go u
          | None => StOpaque
          end
      | TPat base _ => go base
      | TAdt path args =>
          match find_adt adts path with
          | Some d =>
              let r := reprs_of (ad_repr d) in
              match ad_kind d, ad_variants d with
              | AkStruct, [v] => StStruct path (map go (variant_field_tys args v)) r
              | AkUnion, [v] => StUnion path (map go (variant_field_tys args v)) r
              | AkEnum, vs =>
                  StEnum path (map (fun v => map go (variant_field_tys args v)) vs) r
              | _, _ => StOpaque
              end
          | None => StOpaque
          end
      | _ => StOpaque
      end
  end.

Definition syn_type_of (adts : list adt_def) (t : ty) : syn_type :=
  syn_type_of_fuel 64 adts t.

Definition size_align := (nat * nat)%type.

Record agg_layout := AggLayout {
  ag_size : nat;
  ag_align : nat;
  ag_offsets : list nat;
}.

Record enum_layout := EnumLayout {
  en_size : nat;
  en_align : nat;
  en_tag : scalar_layout;
  en_tag_offset : nat;
  en_variants : list agg_layout;
}.

Definition max_isize : Z := (2 ^ 63 - 1)%Z.

Definition size_ok (n : nat) : bool := (Z.of_nat n <=? max_isize)%Z.

Lemma size_ok_le : forall n, size_ok n = true -> (Z.of_nat n <= max_isize)%Z.
Proof. intros n H. apply Z.leb_le. exact H. Qed.

Definition fits (off size total : nat) : Prop := off + size <= total.
Definition aligned (align off : nat) : Prop := Nat.modulo off align = 0.

Definition apart (o1 s1 o2 s2 : nat) : Prop := o1 + s1 <= o2 \/ o2 + s2 <= o1.

Fixpoint pairwise_apart (rs : list (nat * nat)) : Prop :=
  match rs with
  | [] => True
  | (o, s) :: rest =>
      Forall (fun r => apart o s (fst r) (snd r)) rest /\ pairwise_apart rest
  end.

Definition fields_placed (fs : list size_align) (l : agg_layout) : Prop :=
  length (ag_offsets l) = length fs
  /\ Forall2 (fun f off => fits off (fst f) (ag_size l) /\ aligned (snd f) off)
             fs (ag_offsets l)
  /\ pairwise_apart (combine (ag_offsets l) (map fst fs)).

Definition union_placed (fs : list size_align) (l : agg_layout) : Prop :=
  length (ag_offsets l) = length fs
  /\ Forall2 (fun f off => fits off (fst f) (ag_size l) /\ aligned (snd f) off)
             fs (ag_offsets l).

Definition agg_wf (l : agg_layout) : Prop :=
  1 <= ag_align l
  /\ aligned (ag_align l) (ag_size l)
  /\ (Z.of_nat (ag_size l) <= max_isize)%Z.

Definition scalar_bytes (s : scalar_layout) : nat :=
  match scalar_primitive s with
  | PrimInt bits _ => Nat.div bits 8
  | PrimFloat bits => Nat.div bits 8
  | PrimPointer _ bits => Nat.div bits 8
  end.

Definition variant_placed (tag_off tag_size size : nat) (fs : list size_align)
    (v : agg_layout) : Prop :=
  fields_placed fs v
  /\ ag_size v <= size
  /\ Forall (fun r => apart tag_off tag_size (fst r) (snd r))
            (combine (ag_offsets v) (map fst fs)).

Class LayoutAlg := {
  struct_alg : name -> list size_align -> list repr -> option agg_layout;
  union_alg : name -> list size_align -> list repr -> option agg_layout;
  enum_alg : name -> list (list size_align) -> list repr -> option enum_layout;

  struct_alg_placed : forall n fs r l,
    struct_alg n fs r = Some l -> fields_placed fs l;
  struct_alg_wf : forall n fs r l,
    struct_alg n fs r = Some l -> agg_wf l;

  union_alg_placed : forall n fs r l,
    union_alg n fs r = Some l -> union_placed fs l;
  union_alg_wf : forall n fs r l,
    union_alg n fs r = Some l -> agg_wf l;

  enum_alg_variants : forall n vs r l,
    enum_alg n vs r = Some l ->
    length (en_variants l) = length vs
    /\ Forall2 (variant_placed (en_tag_offset l) (scalar_bytes (en_tag l)) (en_size l))
               vs (en_variants l);
  enum_alg_tag : forall n vs r l,
    enum_alg n vs r = Some l ->
    fits (en_tag_offset l) (scalar_bytes (en_tag l)) (en_size l)
    /\ scalar_valid_start (en_tag l) = 0%Z
    /\ scalar_valid_end (en_tag l) = (Z.of_nat (length vs) - 1)%Z;
  enum_alg_wf : forall n vs r l,
    enum_alg n vs r = Some l ->
    1 <= en_align l
    /\ aligned (en_align l) (en_size l)
    /\ (Z.of_nat (en_size l) <= max_isize)%Z;
}.

Inductive layout_tree :=
  | LtPrim (size align : nat)
  | LtArray (elem : layout_tree) (len : nat)
  | LtAgg (l : agg_layout) (fields : list layout_tree)
  | LtEnum (l : enum_layout) (variants : list (list layout_tree)).

Fixpoint lt_size (lt : layout_tree) : nat :=
  match lt with
  | LtPrim s _ => s
  | LtArray e n => n * lt_size e
  | LtAgg l _ => ag_size l
  | LtEnum l _ => en_size l
  end.

Fixpoint lt_align (lt : layout_tree) : nat :=
  match lt with
  | LtPrim _ a => a
  | LtArray e _ => lt_align e
  | LtAgg l _ => ag_align l
  | LtEnum l _ => en_align l
  end.

Definition sa_of (lt : layout_tree) : size_align := (lt_size lt, lt_align lt).

Fixpoint all_some {A} (xs : list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | None :: _ => None
  | Some x :: rest => match all_some rest with
                      | Some ys => Some (x :: ys)
                      | None => None
                      end
  end.

Section UseLayoutAlg.
  Context {A : LayoutAlg}.

  Fixpoint use_layout_alg (st : syn_type) : option layout_tree :=
    match st with
    | StInt w _ => Some (LtPrim (int_width_bytes w) (int_width_bytes w))
    | StBool => Some (LtPrim 1 1)
    | StChar => Some (LtPrim 4 4)
    | StFloat w =>
        Some (LtPrim (Nat.div (float_width_bits w) 8) (Nat.div (float_width_bits w) 8))
    | StPtr fat =>
        Some (LtPrim (if fat then 2 * pointer_bytes else pointer_bytes) pointer_bytes)
    | StFnPtr => Some (LtPrim pointer_bytes pointer_bytes)
    | StUnit | StNever => Some (LtPrim 0 1)
    | StArray e n =>
        match use_layout_alg e with
        | Some lt => Some (LtArray lt n)
        | None => None
        end
    | StTuple fs =>
        match all_some (map use_layout_alg fs) with
        | Some lts =>
            match struct_alg "" (map sa_of lts) [] with
            | Some l => Some (LtAgg l lts)
            | None => None
            end
        | None => None
        end
    | StStruct path fs r =>
        match all_some (map use_layout_alg fs) with
        | Some lts =>
            match struct_alg path (map sa_of lts) r with
            | Some l => Some (LtAgg l lts)
            | None => None
            end
        | None => None
        end
    | StUnion path fs r =>
        match all_some (map use_layout_alg fs) with
        | Some lts =>
            match union_alg path (map sa_of lts) r with
            | Some l => Some (LtAgg l lts)
            | None => None
            end
        | None => None
        end
    | StEnum path vs r =>
        match all_some (map (fun fs => all_some (map use_layout_alg fs)) vs) with
        | Some vlts =>
            match enum_alg path (map (map sa_of) vlts) r with
            | Some l => Some (LtEnum l vlts)
            | None => None
            end
        | None => None
        end
    | StUnsized | StOpaque => None
    end.
End UseLayoutAlg.

Definition variant_of (idx : nat) (tys : list ty) (v : agg_layout) : variant_layout :=
  VariantLayoutWithFields idx (ag_size v) false tys (ag_offsets v) (AbiMemory true).

Definition tag_ty (s : scalar_layout) : ty :=
  match scalar_primitive s with
  | PrimInt 8 false => TUint W8
  | PrimInt 16 false => TUint W16
  | PrimInt 32 false => TUint W32
  | PrimInt 64 false => TUint W64
  | PrimInt 8 true => TInt W8
  | PrimInt 16 true => TInt W16
  | PrimInt 32 true => TInt W32
  | PrimInt 64 true => TInt W64
  | _ => TUint WSize
  end.

Definition adt_field_tys (adts : list adt_def) (t : ty) : option (list ty) :=
  match t with
  | TTuple ts => Some ts
  | TAdt path args =>
      match find_adt adts path with
      | Some d =>
          match ad_variants d with
          | [v] => Some (variant_field_tys args v)
          | _ => Some []
          end
      | None => None
      end
  | _ => Some []
  end.

Definition adt_kind_of (adts : list adt_def) (t : ty) : option adt_kind :=
  match t with
  | TAdt path _ =>
      match find_adt adts path with
      | Some d => Some (ad_kind d)
      | None => None
      end
  | _ => None
  end.

Definition type_layout_of_tree (adts : list adt_def) (t : ty) (lt : layout_tree)
    : option type_layout :=
  match lt with
  | LtPrim s a =>
      Some (TypeLayoutWithFields "alg" t s a false [] FieldsPrimitive
              (VariantsSingle 0) (AbiMemory true))
  | LtArray e n =>
      Some (TypeLayoutWithFields "alg" t (lt_size lt) (lt_align lt) false []
              (FieldsArray (lt_size e) n) (VariantsSingle 0) (AbiMemory true))
  | LtAgg l _ =>
      match adt_field_tys adts t with
      | Some tys =>
          let fl := match adt_kind_of adts t with
                    | Some AkUnion => FieldsUnion (length tys)
                    | _ => FieldsArbitrary (ag_offsets l)
                    end in
          Some (TypeLayoutWithFields "alg" t (ag_size l) (ag_align l) false tys fl
                  (VariantsSingle 0) (AbiMemory true))
      | None => None
      end
  | LtEnum l _ =>
      match t with
      | TAdt path args =>
          match find_adt adts path with
          | Some d =>
              let variants :=
                map (fun (p : variant_def * agg_layout) =>
                       variant_of (vd_index (fst p)) (variant_field_tys args (fst p)) (snd p))
                    (combine (ad_variants d) (en_variants l)) in
              Some (TypeLayoutWithFields "alg" t (en_size l) (en_align l) false
                      [tag_ty (en_tag l)] (FieldsArbitrary [en_tag_offset l])
                      (VariantsMultiple (en_tag l) 0 TagDirect variants)
                      (AbiMemory true))
          | None => None
          end
      | _ => None
      end
  end.

Definition type_layout_of {A : LayoutAlg} (adts : list adt_def) (t : ty)
    : option type_layout :=
  match use_layout_alg (syn_type_of adts t) with
  | Some lt => type_layout_of_tree adts t lt
  | None => None
  end.

Fixpoint reachable_tys_fuel (fuel : nat) (adts : list adt_def) (t : ty) : list ty :=
  match fuel with
  | O => []
  | S fuel =>
      let go := reachable_tys_fuel fuel adts in
      match t with
      | TClosure _ args =>
          match closure_upvars args with
          | Some u => go u
          | None => []
          end
      | _ =>
          t :: match t with
               | TTuple ts => List.concat (map go ts)
               | TArray e _ | TSlice e => go e
               | TRef _ p _ | TRawPtr p _ => go p
               | TPat base _ => go base
               | TAdt path args =>
                   match find_adt adts path with
                   | Some d =>
                       List.concat (map (fun v => List.concat (map go (variant_field_tys args v)))
                                   (ad_variants d))
                   | None => []
                   end
               | _ => []
               end
      end
  end.

Fixpoint dedup_tys (acc : list ty) (ts : list ty) : list ty :=
  match ts with
  | [] => rev acc
  | t :: rest =>
      if existsb (ty_eqb t) acc then dedup_tys acc rest else dedup_tys (t :: acc) rest
  end.

Definition layout_env_of {A : LayoutAlg} (adts : list adt_def) (ts : list ty)
    : layout_env :=
  let all := dedup_tys [] (List.concat (map (reachable_tys_fuel 8 adts) ts)) in
  fold_right (fun t acc => match type_layout_of adts t with
                           | Some l => l :: acc
                           | None => acc
                           end)
             [] all.

Definition align_to (off a : nat) : nat := Nat.div (off + a - 1) a * a.

Lemma align_to_aligned : forall off a, a <> 0 -> aligned a (align_to off a).
Proof. intros off a Ha. unfold aligned, align_to. apply Nat.Div0.mod_mul. Qed.

Lemma align_to_ge : forall off a, a <> 0 -> off <= align_to off a.
Proof.
  intros off a Ha. unfold align_to. rewrite Nat.mul_comm.
  pose proof (Nat.div_mod_eq (off + a - 1) a) as Hdm.
  pose proof (Nat.mod_upper_bound (off + a - 1) a Ha) as Hub.
  lia.
Qed.

Definition aligns_pos (fs : list size_align) : Prop :=
  Forall (fun f => snd f <> 0) fs.

Definition aligns_ok (fs : list size_align) : bool :=
  forallb (fun f => negb (Nat.eqb (snd f) 0)) fs.

Lemma aligns_ok_pos : forall fs, aligns_ok fs = true -> aligns_pos fs.
Proof.
  induction fs as [|f fs IH]; intros H; [constructor|].
  simpl in H. apply andb_prop in H as [Hf Hrest].
  constructor; [|apply IH; assumption].
  destruct (Nat.eqb (snd f) 0) eqn:E; [discriminate|].
  apply Nat.eqb_neq in E. assumption.
Qed.

Fixpoint c_offsets (at_ : nat) (fs : list size_align) : list nat :=
  match fs with
  | [] => []
  | f :: rest =>
      let o := align_to at_ (snd f) in o :: c_offsets (o + fst f) rest
  end.

Fixpoint c_end (at_ : nat) (fs : list size_align) : nat :=
  match fs with
  | [] => at_
  | f :: rest => c_end (align_to at_ (snd f) + fst f) rest
  end.

Definition c_align (fs : list size_align) : nat :=
  fold_right (fun f acc => Nat.max (snd f) acc) 1 fs.

Definition max_size (fs : list size_align) : nat :=
  fold_right (fun f acc => Nat.max (fst f) acc) 0 fs.

Lemma c_align_pos : forall fs, 1 <= c_align fs.
Proof. induction fs as [|f fs IH]; simpl; lia. Qed.

Lemma c_align_nz : forall fs, c_align fs <> 0.
Proof. intros fs. pose proof (c_align_pos fs). lia. Qed.

Lemma c_offsets_length : forall fs at_, length (c_offsets at_ fs) = length fs.
Proof. induction fs as [|f fs IH]; intros; simpl; auto. Qed.

Lemma c_end_ge : forall fs at_, aligns_pos fs -> at_ <= c_end at_ fs.
Proof.
  induction fs as [|f fs IH]; intros at_ Ha; simpl; [lia|].
  inversion Ha as [|? ? Hf Hrest]; subst.
  pose proof (align_to_ge at_ (snd f) Hf).
  specialize (IH (align_to at_ (snd f) + fst f) Hrest). lia.
Qed.

Lemma c_offsets_ge : forall fs at_,
  aligns_pos fs -> Forall (fun o => at_ <= o) (c_offsets at_ fs).
Proof.
  induction fs as [|f fs IH]; intros at_ Ha; simpl; [constructor|].
  inversion Ha as [|? ? Hf Hrest]; subst.
  pose proof (align_to_ge at_ (snd f) Hf).
  constructor; [lia|].
  eapply Forall_impl; [|apply (IH (align_to at_ (snd f) + fst f) Hrest)].
  simpl. lia.
Qed.

Lemma c_offsets_placed : forall fs at_ size,
  aligns_pos fs -> c_end at_ fs <= size ->
  Forall2 (fun f o => fits o (fst f) size /\ aligned (snd f) o) fs (c_offsets at_ fs).
Proof.
  induction fs as [|f fs IH]; intros at_ size Ha Hsz; simpl in *; [constructor|].
  inversion Ha as [|? ? Hf Hrest]; subst.
  constructor.
  - split; [|apply align_to_aligned; assumption].
    unfold fits.
    pose proof (c_end_ge fs (align_to at_ (snd f) + fst f) Hrest). lia.
  - apply IH; assumption.
Qed.

Lemma forall_combine_left :
  forall (P : nat -> Prop) (offs : list nat) (sizes : list nat),
  Forall P offs -> Forall (fun r => P (fst r)) (combine offs sizes).
Proof.
  induction offs as [|o offs IH]; intros sizes H; destruct sizes as [|s sizes];
    simpl; try constructor.
  - inversion H; subst; assumption.
  - apply IH. inversion H; subst; assumption.
Qed.

Lemma c_offsets_apart : forall fs at_,
  aligns_pos fs -> pairwise_apart (combine (c_offsets at_ fs) (map fst fs)).
Proof.
  induction fs as [|f fs IH]; intros at_ Ha; simpl; [exact I|].
  inversion Ha as [|? ? Hf Hrest]; subst.
  split; [|apply (IH (align_to at_ (snd f) + fst f) Hrest)].
  eapply Forall_impl;
    [|apply forall_combine_left;
      apply (c_offsets_ge fs (align_to at_ (snd f) + fst f) Hrest)].
  intros r Hr. unfold apart. left. exact Hr.
Qed.

Lemma forall_apart_of_ge : forall (rs : list (nat * nat)) o s base,
  o + s <= base -> Forall (fun r => base <= fst r) rs ->
  Forall (fun r => apart o s (fst r) (snd r)) rs.
Proof.
  induction rs as [|r rs IH]; intros o s base Hb H; [constructor|].
  inversion H; subst.
  constructor; [unfold apart; left; lia | eapply IH; eassumption].
Qed.

Lemma c_offsets_after : forall fs at_ o s,
  aligns_pos fs -> o + s <= at_ ->
  Forall (fun r => apart o s (fst r) (snd r))
         (combine (c_offsets at_ fs) (map fst fs)).
Proof.
  intros fs at_ o s Ha Hle.
  eapply forall_apart_of_ge; [exact Hle|].
  apply forall_combine_left. apply c_offsets_ge. assumption.
Qed.

Lemma c_fields_placed : forall fs at_ size,
  aligns_pos fs -> c_end at_ fs <= size ->
  fields_placed fs (AggLayout size (c_align fs) (c_offsets at_ fs)).
Proof.
  intros fs at_ size Ha Hsz. unfold fields_placed; simpl.
  split; [apply c_offsets_length|].
  split; [apply c_offsets_placed; assumption | apply c_offsets_apart; assumption].
Qed.

Definition c_struct (fs : list size_align) : option agg_layout :=
  let a := c_align fs in
  let sz := align_to (c_end 0 fs) a in
  if aligns_ok fs && size_ok sz
  then Some (AggLayout sz a (c_offsets 0 fs))
  else None.

Definition c_union (fs : list size_align) : option agg_layout :=
  let a := c_align fs in
  let sz := align_to (max_size fs) a in
  if aligns_ok fs && size_ok sz
  then Some (AggLayout sz a (repeat 0 (length fs)))
  else None.

Definition tag_bytes : nat := 4.

Definition tag_for (variants : nat) : scalar_layout :=
  ScalarLayout (PrimInt (8 * tag_bytes) false) true 0%Z
    (Z.of_nat variants - 1)%Z.

Definition c_variant (fs : list size_align) : agg_layout :=
  AggLayout (c_end tag_bytes fs) (c_align fs) (c_offsets tag_bytes fs).

Definition enum_align (vs : list agg_layout) : nat :=
  fold_right (fun v acc => Nat.max (ag_align v) acc) tag_bytes vs.

Definition enum_extent (vs : list agg_layout) : nat :=
  fold_right (fun v acc => Nat.max (ag_size v) acc) tag_bytes vs.

Definition c_enum (vs : list (list size_align)) : option enum_layout :=
  let variants := map c_variant vs in
  let a := enum_align variants in
  let sz := align_to (enum_extent variants) a in
  if forallb aligns_ok vs && size_ok sz
  then Some (EnumLayout sz a (tag_for (length vs)) 0 variants)
  else None.

Lemma c_struct_placed : forall (n : name) fs (r : list repr) l,
  c_struct fs = Some l -> fields_placed fs l.
Proof.
  intros n fs r l H. unfold c_struct in H.
  destruct (aligns_ok fs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok (align_to (c_end 0 fs) (c_align fs))) eqn:Es;
    [|discriminate].
  injection H as <-.
  apply c_fields_placed; [apply aligns_ok_pos; assumption|].
  apply align_to_ge, c_align_nz.
Qed.

Lemma c_struct_wf : forall (n : name) fs (r : list repr) l,
  c_struct fs = Some l -> agg_wf l.
Proof.
  intros n fs r l H. unfold c_struct in H.
  destruct (aligns_ok fs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok (align_to (c_end 0 fs) (c_align fs))) eqn:Es;
    [|discriminate].
  injection H as <-. unfold agg_wf; simpl.
  split; [apply c_align_pos|].
  split; [apply align_to_aligned, c_align_nz | apply size_ok_le; assumption].
Qed.

Lemma repeat_zero_placed : forall fs total,
  aligns_pos fs -> Forall (fun f => fst f <= total) fs ->
  Forall2 (fun f o => fits o (fst f) total /\ aligned (snd f) o)
          fs (repeat 0 (length fs)).
Proof.
  induction fs as [|f fs IH]; intros total Ha Hs; simpl; [constructor|].
  inversion Ha; subst. inversion Hs; subst.
  constructor; [|apply IH; assumption].
  split; [unfold fits; lia|].
  unfold aligned. apply Nat.Div0.mod_0_l.
Qed.

Lemma max_size_ge : forall fs, Forall (fun f => fst f <= max_size fs) fs.
Proof.
  induction fs as [|f fs IH]; [constructor|].
  constructor.
  - unfold max_size; simpl; lia.
  - eapply Forall_impl; [|exact IH].
    intros g Hg. unfold max_size in *; simpl; lia.
Qed.

Lemma forall_size_le_trans : forall (fs : list size_align) (a b : nat),
  Forall (fun f => fst f <= a) fs -> a <= b -> Forall (fun f => fst f <= b) fs.
Proof.
  induction fs as [|f fs IH]; intros a b H Hab; [constructor|].
  inversion H; subst. constructor; [lia | eapply IH; eassumption].
Qed.

Lemma c_union_placed : forall (n : name) fs (r : list repr) l,
  c_union fs = Some l -> union_placed fs l.
Proof.
  intros n fs r l H. unfold c_union in H.
  destruct (aligns_ok fs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok (align_to (max_size fs) (c_align fs))) eqn:Es;
    [|discriminate].
  injection H as <-. unfold union_placed; simpl.
  split; [apply repeat_length|].
  apply repeat_zero_placed; [apply aligns_ok_pos; assumption|].
  eapply forall_size_le_trans; [apply max_size_ge|].
  apply align_to_ge, c_align_nz.
Qed.

Lemma c_union_wf : forall (n : name) fs (r : list repr) l,
  c_union fs = Some l -> agg_wf l.
Proof.
  intros n fs r l H. unfold c_union in H.
  destruct (aligns_ok fs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok (align_to (max_size fs) (c_align fs))) eqn:Es;
    [|discriminate].
  injection H as <-. unfold agg_wf; simpl.
  split; [apply c_align_pos|].
  split; [apply align_to_aligned, c_align_nz | apply size_ok_le; assumption].
Qed.

Lemma enum_extent_ge : forall vs, Forall (fun v => ag_size v <= enum_extent vs) vs.
Proof.
  induction vs as [|v vs IH]; simpl; constructor; [unfold enum_extent; simpl; lia|].
  eapply Forall_impl; [|exact IH].
  intros w Hw. unfold enum_extent in *; simpl; lia.
Qed.

Lemma enum_extent_base : forall vs, tag_bytes <= enum_extent vs.
Proof. induction vs as [|v vs IH]; unfold enum_extent in *; simpl; lia. Qed.

Lemma enum_align_nz : forall vs, enum_align vs <> 0.
Proof.
  induction vs as [|v vs IH]; unfold enum_align, tag_bytes in *; simpl; lia.
Qed.

Lemma scalar_bytes_tag : forall n, scalar_bytes (tag_for n) = tag_bytes.
Proof. reflexivity. Qed.

Lemma c_variants_placed : forall vs size,
  Forall (fun fs => aligns_ok fs = true) vs ->
  Forall (fun v => ag_size v <= size) (map c_variant vs) ->
  Forall2 (variant_placed 0 tag_bytes size) vs (map c_variant vs).
Proof.
  induction vs as [|fs vs IH]; intros size Hok Hsz; simpl in *; [constructor|].
  inversion Hok; subst. inversion Hsz; subst.
  assert (Hp : aligns_pos fs) by (apply aligns_ok_pos; assumption).
  constructor; [|apply IH; assumption].
  unfold variant_placed, c_variant; simpl.
  split; [apply c_fields_placed; [assumption | lia]|].
  split; [assumption|].
  apply c_offsets_after; [assumption | unfold tag_bytes; lia].
Qed.

Lemma forallb_forall_true : forall (A : Type) (f : A -> bool) (l : list A),
  forallb f l = true -> Forall (fun x => f x = true) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  simpl in H. apply andb_prop in H as [Hx Hl].
  constructor; [assumption | apply IH; assumption].
Qed.

Lemma forall_ag_size_le_trans : forall (vs : list agg_layout) (a b : nat),
  Forall (fun v => ag_size v <= a) vs -> a <= b ->
  Forall (fun v => ag_size v <= b) vs.
Proof.
  induction vs as [|v vs IH]; intros a b H Hab; [constructor|].
  inversion H; subst. constructor; [lia | eapply IH; eassumption].
Qed.

Lemma c_enum_variants : forall (n : name) vs (r : list repr) l,
  c_enum vs = Some l ->
  length (en_variants l) = length vs
  /\ Forall2 (variant_placed (en_tag_offset l) (scalar_bytes (en_tag l)) (en_size l))
             vs (en_variants l).
Proof.
  intros n vs r l H. unfold c_enum in H.
  destruct (forallb aligns_ok vs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok _) eqn:Es; [|discriminate].
  injection H as <-. simpl.
  split; [apply length_map|].
  rewrite scalar_bytes_tag.
  apply c_variants_placed; [apply forallb_forall_true; assumption|].
  eapply forall_ag_size_le_trans; [apply enum_extent_ge|].
  apply align_to_ge, enum_align_nz.
Qed.

Lemma c_enum_tag : forall (n : name) vs (r : list repr) l,
  c_enum vs = Some l ->
  fits (en_tag_offset l) (scalar_bytes (en_tag l)) (en_size l)
  /\ scalar_valid_start (en_tag l) = 0%Z
  /\ scalar_valid_end (en_tag l) = (Z.of_nat (length vs) - 1)%Z.
Proof.
  intros n vs r l H. unfold c_enum in H.
  destruct (forallb aligns_ok vs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok _) eqn:Es; [|discriminate].
  injection H as <-. simpl.
  split; [|split; reflexivity].
  rewrite scalar_bytes_tag. unfold fits; simpl.
  pose proof (enum_extent_base (map c_variant vs)).
  pose proof (align_to_ge (enum_extent (map c_variant vs))
                (enum_align (map c_variant vs))
                (enum_align_nz (map c_variant vs))).
  lia.
Qed.

Lemma c_enum_wf : forall (n : name) vs (r : list repr) l,
  c_enum vs = Some l ->
  1 <= en_align l /\ aligned (en_align l) (en_size l)
  /\ (Z.of_nat (en_size l) <= max_isize)%Z.
Proof.
  intros n vs r l H. unfold c_enum in H.
  destruct (forallb aligns_ok vs) eqn:Ea; simpl in H; [|discriminate].
  destruct (size_ok _) eqn:Es; [|discriminate].
  injection H as <-. simpl.
  pose proof (enum_align_nz (map c_variant vs)).
  split; [lia|].
  split; [apply align_to_aligned; assumption | apply size_ok_le; assumption].
Qed.

#[global] Instance CAlg : LayoutAlg := {
  struct_alg := fun _ fs _ => c_struct fs;
  union_alg := fun _ fs _ => c_union fs;
  enum_alg := fun _ vs _ => c_enum vs;
  struct_alg_placed := c_struct_placed;
  struct_alg_wf := c_struct_wf;
  union_alg_placed := c_union_placed;
  union_alg_wf := c_union_wf;
  enum_alg_variants := c_enum_variants;
  enum_alg_tag := c_enum_tag;
  enum_alg_wf := c_enum_wf;
}.

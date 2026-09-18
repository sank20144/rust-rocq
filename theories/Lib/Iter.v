From RustRocq Require Import Syntax LayoutAlg Memory Denote Lib.Models Lib.Core Lib.Bitvec.
From Stdlib Require Import Bool String List ZArith Lia.
Import ListNotations.

Local Open Scope string_scope.

Definition scan_path : name := "core::iter::Scan".
Definition enumerate_path : name := "core::iter::Enumerate".
Definition iter_ones_path : name := "bitvec::slice::IterOnes".
Definition windows_path : name := "bitvec::slice::Windows".

Definition closure_of (t : ty) : option (name * list garg) :=
  match t with
  | TClosure p args => Some (p, args)
  | _ => None
  end.

Definition ones_of (ws : list Z) (s : slice_view) : list nat :=
  filter (fun i => bit_of ws (sv_head s + i)) (seq 0 (sv_len s)).

Definition option_of (best : option (Z * runtime_value)) : runtime_value :=
  match best with
  | Some (_, x) => some_value x
  | None => none_value
  end.

Definition keep_max (best : option (Z * runtime_value)) (k : Z) (x : runtime_value)
    : option (Z * runtime_value) :=
  match best with
  | Some (bk, bx) => if Z.ltb k bk then Some (bk, bx) else Some (k, x)
  | None => Some (k, x)
  end.

Definition window_count (s : slice_view) (width : nat) : nat :=
  if Nat.leb width (sv_len s) then sv_len s - width + 1 else 0.

Definition input_pointee (t : ty) : option ty :=
  match t with
  | TClosure _ args =>
      match closure_inputs args with
      | [TRef _ item _] => Some item
      | _ => None
      end
  | _ => None
  end.

Definition windows_value (s : slice_view) (width : nat) : runtime_value :=
  VAdt windows_path 0 [view_value s; VBits WSize (Z.of_nat width)].

Section Models.

Context `{Alg : LayoutAlg}.

Fixpoint max_scan_loop (cb : call_back) (adts : list adt_def)
    (step : name * list garg) (step_ptr state_ptr : runtime_value)
    (key : name * list garg) (key_ptr : runtime_value) (item_ty : ty)
    (front : Z) (idxs : list nat) (best : option (Z * runtime_value))
    : HM runtime_value :=
  match idxs with
  | [] => hret (option_of best)
  | i :: rest =>
      hbind (hcall cb (fst step) (snd step)
               [step_ptr; state_ptr; VBits WSize (front + Z.of_nat i)]) (fun r =>
      match r with
      | VAdt _ 1 [x] =>
          hbind (alloc_temp adts item_ty x) (fun xp =>
          hbind (hcall cb (fst key) (snd key) [key_ptr; xp]) (fun k =>
          hbind (free_temp xp) (fun _ =>
          match k with
          | VBits _ kz =>
              max_scan_loop cb adts step step_ptr state_ptr key key_ptr item_ty front rest
                (keep_max best kz x)
          | _ => hfail "a max_by_key key that is not an integer"
          end)))
      | _ => hret (option_of best)
      end)
  end.

Lemma max_scan_loop_mono adts step step_ptr state_ptr key key_ptr item_ty front :
  forall idxs best,
    hmono (fun cb =>
      max_scan_loop cb adts step step_ptr state_ptr key key_ptr item_ty front idxs best).
Proof.
  induction idxs as [|i rest IH]; intros best; cbn [max_scan_loop].
  - apply hret_mono.
  - apply hbind_mono; [apply hcall_mono|]. intros r.
    destruct r as [| | | | | | |p v xs]; try apply hret_mono.
    destruct v as [|[|]]; try apply hret_mono.
    destruct xs as [|x [|]]; try apply hret_mono.
    apply hbind_mono; [apply hconst_mono|]. intros xp.
    apply hbind_mono; [apply hcall_mono|]. intros k.
    apply hbind_mono; [apply hconst_mono|]. intros u.
    destruct k; try apply hfail_mono. apply IH.
Qed.

Definition max_by_key_model (adts : list adt_def) (targs : list garg) (vs : list runtime_value)
    : option (call_back -> HM runtime_value) :=
  match targs, vs with
  | [GTy (TAdt p [GTy _; GTy st_ty; GTy step_ty]); GTy _; GTy key_ty],
    [VAdt _ 0 [VAdt _ 0 [slice; VBits _ front]; step_val; state_val]; key_val] =>
      if String.eqb p scan_path then
        match view_of slice, closure_of step_ty, closure_of key_ty, input_pointee key_ty with
        | Some s, Some step, Some key, Some item_ty =>
            Some (fun cb =>
              hbind (hlift (read_view adts s)) (fun ws =>
              hbind (alloc_temp adts step_ty step_val) (fun step_ptr =>
              hbind (alloc_temp adts st_ty state_val) (fun state_ptr =>
              hbind (alloc_temp adts key_ty key_val) (fun key_ptr =>
              hbind (max_scan_loop cb adts step step_ptr state_ptr key key_ptr item_ty front
                       (ones_of ws s) None) (fun r =>
              hbind (free_temp step_ptr) (fun _ =>
              hbind (free_temp state_ptr) (fun _ =>
              hbind (free_temp key_ptr) (fun _ => hret r)))))))))
        | _, _, _, _ => None
        end
      else None
  | _, _ => None
  end.

Lemma max_by_key_model_mono adts targs vs m :
  max_by_key_model adts targs vs = Some m -> hmono m.
Proof.
  unfold max_by_key_model. intros H.
  repeat match type of H with
         | match ?x with _ => _ end = Some _ => destruct x; try discriminate
         | (if ?b then _ else _) = Some _ => destruct b; try discriminate
         end.
  injection H as <-.
  apply hbind_mono; [apply hconst_mono|]. intros ws0.
  apply hbind_mono; [apply hconst_mono|]. intros sp.
  apply hbind_mono; [apply hconst_mono|]. intros stp.
  apply hbind_mono; [apply hconst_mono|]. intros kp.
  apply hbind_mono; [apply max_scan_loop_mono|]. intros res.
  repeat (apply hbind_mono; [apply hconst_mono|]; intros ?).
  apply hret_mono.
Qed.

Fixpoint find_windows_loop (cb : call_back) (adts : list adt_def)
    (pred : name * list garg) (pred_ptr : runtime_value) (item_ty : ty)
    (s : slice_view) (width : nat) (count : Z) (i : nat) (fuel : nat)
    : HM (option (nat * runtime_value)) :=
  match fuel with
  | O => hret None
  | S fuel =>
      let item := VTuple [VBits WSize (count + Z.of_nat i);
                          view_value (sub_view s i (i + width))] in
      hbind (alloc_temp adts item_ty item) (fun ip =>
      hbind (hcall cb (fst pred) (snd pred) [pred_ptr; ip]) (fun b =>
      hbind (free_temp ip) (fun _ =>
      match b with
      | VBool true => hret (Some (i, item))
      | VBool false => find_windows_loop cb adts pred pred_ptr item_ty s width count (S i) fuel
      | _ => hfail "a find predicate that did not return a bool"
      end)))
  end.

Lemma find_windows_loop_mono adts pred pred_ptr item_ty s width count :
  forall fuel i,
    hmono (fun cb => find_windows_loop cb adts pred pred_ptr item_ty s width count i fuel).
Proof.
  induction fuel as [|fuel IH]; intros i; cbn [find_windows_loop].
  - apply hret_mono.
  - apply hbind_mono; [apply hconst_mono|]. intros ip.
    apply hbind_mono; [apply hcall_mono|]. intros b.
    apply hbind_mono; [apply hconst_mono|]. intros u.
    destruct b as [|[|]| | | | | |]; try apply hfail_mono;
      [apply hret_mono | apply IH].
Qed.

Definition find_model (adts : list adt_def) (targs : list garg) (vs : list runtime_value)
    : option (call_back -> HM runtime_value) :=
  match targs, vs with
  | [GTy (TAdt e [GTy (TAdt w _)] as self_ty); GTy pred_ty], [self_ptr; pred_val] =>
      if String.eqb e enumerate_path && String.eqb w windows_path then
        match closure_of pred_ty, input_pointee pred_ty with
        | Some pred, Some item_ty =>
            Some (fun cb =>
              hbind (hlift (read_arg adts self_ty self_ptr)) (fun it =>
              match it with
              | VAdt _ 0 [VAdt _ 0 [slice; VBits _ width]; VBits _ count] =>
                  match view_of slice with
                  | Some s =>
                      let wd := Z.to_nat width in
                      hbind (alloc_temp adts pred_ty pred_val) (fun pred_ptr =>
                      hbind (find_windows_loop cb adts pred pred_ptr item_ty s wd count 0
                               (window_count s wd)) (fun found =>
                      hbind (free_temp pred_ptr) (fun _ =>
                      match found with
                      | Some (i, item) =>
                          hbind (hlift (write_arg adts self_ty self_ptr
                                   (VAdt enumerate_path 0
                                      [windows_value (sub_view s (S i) (sv_len s)) wd;
                                       VBits WSize (count + Z.of_nat (S i))]))) (fun _ =>
                          hret (some_value item))
                      | None =>
                          hbind (hlift (write_arg adts self_ty self_ptr
                                   (VAdt enumerate_path 0
                                      [windows_value (sub_view s (sv_len s) (sv_len s)) wd;
                                       VBits WSize (count + Z.of_nat (window_count s wd))])))
                            (fun _ => hret none_value)
                      end)))
                  | None => hfail "Iterator::find over windows of a value that is not a slice"
                  end
              | _ => hfail "Iterator::find over a value that is not enumerated windows"
              end))
        | _, _ => None
        end
      else None
  | _, _ => None
  end.

Lemma find_model_mono adts targs vs m : find_model adts targs vs = Some m -> hmono m.
Proof.
  unfold find_model. intros H.
  repeat match type of H with
         | match ?x with _ => _ end = Some _ => destruct x; try discriminate
         | (if ?b then _ else _) = Some _ => destruct b; try discriminate
         end.
  injection H as <-.
  apply hbind_mono; [apply hconst_mono|]. intros it.
  repeat match goal with
         | |- hmono (fun _ => match ?x with _ => _ end) => destruct x; try apply hfail_mono
         end.
  apply hbind_mono; [apply hconst_mono|]. intros pred_ptr.
  apply hbind_mono; [apply find_windows_loop_mono|]. intros found.
  apply hbind_mono; [apply hconst_mono|]. intros u.
  destruct found as [[i item]|];
    (apply hbind_mono; [apply hconst_mono|]; intros ?; apply hret_mono).
Qed.

Definition option_map_model (targs : list garg) (vs : list runtime_value)
    : option (call_back -> HM runtime_value) :=
  match targs, vs with
  | [GTy _; GTy _; GTy f_ty], [opt; f_val] =>
      match closure_of f_ty with
      | Some f =>
          Some (fun cb =>
            match opt with
            | VAdt p 1 [x] =>
                if String.eqb p option_path
                then hbind (hcall cb (fst f) (snd f) [f_val; x]) (fun y => hret (some_value y))
                else hfail "Option::map of a value that is not an option"
            | VAdt p 0 [] =>
                if String.eqb p option_path then hret none_value
                else hfail "Option::map of a value that is not an option"
            | _ => hfail "Option::map of a value that is not an option"
            end)
      | None => None
      end
  | _, _ => None
  end.

Lemma option_map_model_mono targs vs m : option_map_model targs vs = Some m -> hmono m.
Proof.
  unfold option_map_model. intros H.
  repeat match type of H with
         | match ?x with _ => _ end = Some _ => destruct x; try discriminate
         end.
  injection H as <-.
  repeat match goal with
         | |- hmono (fun _ => match ?x with _ => _ end) => destruct x; try apply hfail_mono
         | |- hmono (fun _ => if ?b then _ else _) => destruct b; try apply hfail_mono
         end;
    try apply hret_mono.
  apply hbind_mono; [apply hcall_mono|]. intros y. apply hret_mono.
Qed.

Definition option_map_or_else_model (targs : list garg) (vs : list runtime_value)
    : option (call_back -> HM runtime_value) :=
  match targs, vs with
  | [GTy _; GTy _; GTy d_ty; GTy f_ty], [opt; d_val; f_val] =>
      match closure_of d_ty, closure_of f_ty with
      | Some d, Some f =>
          Some (fun cb =>
            match opt with
            | VAdt p 1 [x] =>
                if String.eqb p option_path then hcall cb (fst f) (snd f) [f_val; x]
                else hfail "Option::map_or_else of a value that is not an option"
            | VAdt p 0 [] =>
                if String.eqb p option_path then hcall cb (fst d) (snd d) [d_val]
                else hfail "Option::map_or_else of a value that is not an option"
            | _ => hfail "Option::map_or_else of a value that is not an option"
            end)
      | _, _ => None
      end
  | _, _ => None
  end.

Lemma option_map_or_else_model_mono targs vs m :
  option_map_or_else_model targs vs = Some m -> hmono m.
Proof.
  unfold option_map_or_else_model. intros H.
  repeat match type of H with
         | match ?x with _ => _ end = Some _ => destruct x; try discriminate
         end.
  injection H as <-.
  repeat match goal with
         | |- hmono (fun _ => match ?x with _ => _ end) => destruct x; try apply hfail_mono
         | |- hmono (fun _ => if ?b then _ else _) => destruct b; try apply hfail_mono
         end;
    apply hcall_mono.
Qed.

Definition iter_model (adts : list adt_def) (f : name) (targs : list garg)
    (vs : list runtime_value) : option (call_back -> HM runtime_value) :=
  if String.eqb f "core::iter::Iterator::max_by_key" then max_by_key_model adts targs vs
  else if String.eqb f "core::iter::Iterator::find" then find_model adts targs vs
  else if String.eqb f "core::option::Option::<T>::map" then option_map_model targs vs
  else if String.eqb f "core::option::Option::<T>::map_or_else" then
    option_map_or_else_model targs vs
  else None.

Lemma iter_model_mono adts f targs vs m : iter_model adts f targs vs = Some m -> hmono m.
Proof.
  unfold iter_model.
  destruct (String.eqb f "core::iter::Iterator::max_by_key"); [apply max_by_key_model_mono|].
  destruct (String.eqb f "core::iter::Iterator::find"); [apply find_model_mono|].
  destruct (String.eqb f "core::option::Option::<T>::map"); [apply option_map_model_mono|].
  destruct (String.eqb f "core::option::Option::<T>::map_or_else");
    [apply option_map_or_else_model_mono | discriminate].
Qed.

End Models.

Definition iter_constructors : partial_model := fun _ f targs vs =>
  if String.eqb f "bitvec::slice::BitSlice::<T, O>::iter_ones" then
    Some match vs with
         | [x] =>
             match view_of x with
             | Some s => returned (VAdt iter_ones_path 0 [view_value s; VBits WSize 0])
             | None => fail "BitSlice::iter_ones of a value that is not a bit-slice"
             end
         | _ => fail "BitSlice::iter_ones with unexpected arguments"
         end
  else if is_bit_slice_fn f "windows" then
    Some match vs with
         | [x; VBits _ w] =>
             match view_of x with
             | Some s =>
                 if Z.eqb w 0 then panics else returned (windows_value s (Z.to_nat w))
             | None => fail "BitSlice::windows of a value that is not a bit-slice"
             end
         | _ => fail "BitSlice::windows with unexpected arguments"
         end
  else if String.eqb f "core::iter::Iterator::enumerate" then
    Some match vs with
         | [it] => returned (VAdt enumerate_path 0 [it; VBits WSize 0])
         | _ => fail "Iterator::enumerate with unexpected arguments"
         end
  else if String.eqb f "core::iter::Iterator::scan" then
    Some match vs with
         | [it; init; fv] => returned (VAdt scan_path 0 [it; fv; init])
         | _ => fail "Iterator::scan with unexpected arguments"
         end
  else None.

From RustRocq Require Import Syntax Layout Memory Denote Lib.Models Lib.Core.
From Stdlib Require Import String List ZArith Lia.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition bit_array_path : name := "bitvec::array::BitArray".

Definition range_path : name := "core::ops::Range".

Definition bit_array_value (ws : list Z) : runtime_value :=
  VAdt bit_array_path 0 [phantom; VArray (ShapeBits W64) (map (VBits W64) ws)].

Fixpoint words_of_values (vs : list runtime_value) : option (list Z) :=
  match vs with
  | [] => Some []
  | VBits W64 z :: rest => option_map (cons z) (words_of_values rest)
  | _ :: _ => None
  end.

Definition words_of (v : runtime_value) : option (list Z) :=
  match v with
  | VAdt p 0 [_; VArray _ elems] =>
      if String.eqb p bit_array_path then words_of_values elems else None
  | _ => None
  end.

Definition array_words (t : ty) : option nat :=
  match t with
  | TAdt p [GTy (TArray (TUint W64) (CValue _ n)); GTy _] =>
      if String.eqb p bit_array_path then Some (Z.to_nat n) else None
  | _ => None
  end.

Definition word_mask : Z := (2 ^ 64 - 1)%Z.

Definition bit_of (ws : list Z) (i : nat) : bool :=
  Z.testbit (nth (i / 64) ws 0%Z) (Z.of_nat (i mod 64)).

Definition with_bit (ws : list Z) (i : nat) (b : bool) : list Z :=
  let k := i / 64 in
  let w := nth k ws 0%Z in
  let w' := if b then Z.setbit w (Z.of_nat (i mod 64)) else Z.clearbit w (Z.of_nat (i mod 64)) in
  (firstn k ws ++ w' :: skipn (S k) ws)%list.

Definition fill_bits (ws : list Z) (head len : nat) (b : bool) : list Z :=
  fold_left (fun acc i => with_bit acc (head + i) b) (seq 0 len) ws.

Definition first_one_bits (ws : list Z) (head len : nat) : option nat :=
  find (fun i => bit_of ws (head + i)) (seq 0 len).

Definition count_ones_bits (ws : list Z) (head len : nat) : nat :=
  length (filter (fun i => bit_of ws (head + i)) (seq 0 len)).

Definition all_bits (ws : list Z) (head len : nat) : bool :=
  forallb (fun i => bit_of ws (head + i)) (seq 0 len).

Definition bit_slice (prov : pointer_provenance) (word_off : Z) (head len : nat)
    : runtime_value :=
  VPointerValue (ShapeSlice ShapeUnit)
    (PointerValue prov (word_off + 8 * Z.of_nat (head / 64))%Z
       (PointerLength (head mod 64 + 64 * len))).

Record slice_view := SliceView {
  sv_prov : pointer_provenance;
  sv_off : Z;
  sv_head : nat;
  sv_len : nat;
}.

Definition view_of (v : runtime_value) : option slice_view :=
  match v with
  | VPointerValue _ (PointerValue prov off (PointerLength m)) =>
      Some (SliceView prov off (m mod 64) (m / 64))
  | _ => None
  end.

Definition view_words (s : slice_view) : nat := (sv_head s + sv_len s + 63) / 64.

Definition view_value (s : slice_view) : runtime_value :=
  bit_slice (sv_prov s) (sv_off s) (sv_head s) (sv_len s).

Definition sub_view (s : slice_view) (start stop : nat) : slice_view :=
  let h := sv_head s + start in
  SliceView (sv_prov s) (sv_off s + 8 * Z.of_nat (h / 64))%Z (h mod 64) (stop - start).

Definition read_view (env : layout_env) (s : slice_view) : M (list Z) :=
  fun st =>
    match read_through_pointer_result env (ShapeArray (ShapeBits W64) (view_words s))
            (PointerValue (sv_prov s) (sv_off s) PointerThin) st with
    | AccessOk (VArray _ vs) =>
        match words_of_values vs with
        | Some ws => Ok ws st
        | None => Unmodelled "bit-slice words that are not u64"
        end
    | AccessOk _ => Unmodelled "bit-slice words that are not an array"
    | AccessUb r => Ub r
    | AccessFail => Unmodelled "read a bit-slice"
    end.

Definition write_view (env : layout_env) (s : slice_view) (ws : list Z) : M unit :=
  fun st =>
    match write_through_pointer_result env (ShapeArray (ShapeBits W64) (view_words s))
            (PointerValue (sv_prov s) (sv_off s) PointerThin)
            (VArray (ShapeBits W64) (map (VBits W64) ws)) st with
    | AccessOk st' => Ok tt st'
    | AccessUb r => Ub r
    | AccessFail => Unmodelled "write a bit-slice"
    end.

Definition view_of_array (env : layout_env) (t : ty) (p : runtime_value) : option slice_view :=
  match p, array_words t, find_type_layout env t with
  | VPointerValue _ (PointerValue prov off _), Some n, Some l =>
      match layout_field_offset l 1 with
      | Some data => Some (SliceView prov (off + Z.of_nat data)%Z 0 (64 * n))
      | None => None
      end
  | _, _, _ => None
  end.

Definition range_of (v : runtime_value) : option (nat * nat) :=
  match v with
  | VAdt p 0 [VBits _ s; VBits _ e] =>
      if String.eqb p range_path then Some (Z.to_nat s, Z.to_nat e) else None
  | _ => None
  end.

Definition slice_arg (vs : list runtime_value) : option slice_view :=
  match vs with
  | v :: _ => view_of v
  | [] => None
  end.

Definition with_view (vs : list runtime_value) (k : slice_view -> M result) : M result :=
  match slice_arg vs with
  | Some s => k s
  | None => fail "a bit-slice model with an argument that is not a bit-slice"
  end.

Definition is_bit_slice_fn (f suffix : name) : bool :=
  String.eqb f (String.append "bitvec::slice::BitSlice::<T, O>::" suffix)
  || String.eqb f (String.append "bitvec::slice::api::<impl bitvec::slice::BitSlice<T, O>>::"
                     suffix).

Section Models.

Context `{Addr : AddrAlg}.

Definition static_bool (env : layout_env) (b : bool) : M result :=
  fun st =>
    match allocate_typed_value_with_layouts env (state_memory st) ShapeBool (VBool b) with
    | Some (id, memory) => Ok (Returned (VPointer ShapeBool id 0)) (state_with_memory st memory)
    | None => Unmodelled "allocate the static bool of a bit index"
    end.

Definition bitvec_model : partial_model := fun env f targs vs =>
  if String.eqb f "bitvec::array::BitArray::<A, O>::ZERO" then
    match targs with
    | [GTy (TArray (TUint W64) (CValue _ n)); GTy _] =>
        Some (returned (bit_array_value (repeat 0%Z (Z.to_nat n))))
    | _ => None
    end
  else if String.eqb f "bitvec::mem::elts" then
    match targs, vs with
    | [GTy (TUint W64)], [VBits _ n] =>
        Some (returned (VBits WSize (n / 64 + (if Z.eqb (n mod 64) 0 then 0 else 1))%Z))
    | _, _ => None
    end
  else if String.eqb f "core::ops::Not::not" then
    match targs, vs with
    | [GTy t], [v] =>
        match array_words t, words_of v with
        | Some _, Some ws =>
            Some (returned (bit_array_value (map (fun w => Z.lxor w word_mask) ws)))
        | _, _ => None
        end
    | _, _ => None
    end
  else if String.eqb f "core::ops::BitAnd::bitand" then
    match targs, vs with
    | [GTy t; GTy _], [a; b] =>
        match array_words t, words_of a, words_of b with
        | Some _, Some wa, Some wb =>
            Some (returned (bit_array_value (map (fun p => Z.land (fst p) (snd p))
                                                 (combine wa wb))))
        | _, _, _ => None
        end
    | _, _ => None
    end
  else if String.eqb f "core::ops::Deref::deref" || String.eqb f "core::ops::DerefMut::deref_mut"
  then
    match targs, vs with
    | [GTy t], [p] =>
        match array_words t with
        | Some _ =>
            Some match view_of_array env t p with
                 | Some s => returned (view_value s)
                 | None => fail "BitArray::deref without a layout for the array"
                 end
        | None => None
        end
    | _, _ => None
    end
  else if String.eqb f "core::ops::Index::index" || String.eqb f "core::ops::IndexMut::index_mut"
  then
    match targs, vs with
    | [GTy t; GTy (TUint WSize)], [p; VBits _ i] =>
        match array_words t with
        | Some _ =>
            Some match view_of_array env t p with
                 | Some s =>
                     if Nat.leb (sv_len s) (Z.to_nat i) then panics
                     else ws <- read_view env s ;;
                          static_bool env (bit_of ws (sv_head s + Z.to_nat i))
                 | None => fail "BitArray::index without a layout for the array"
                 end
        | None => None
        end
    | [GTy t; GTy _], [p; r] =>
        match array_words t, range_of r with
        | Some _, Some (start, stop) =>
            Some match view_of_array env t p with
                 | Some s =>
                     if Nat.leb start stop && Nat.leb stop (sv_len s)
                     then returned (view_value (sub_view s start stop))
                     else panics
                 | None => fail "BitArray::index without a layout for the array"
                 end
        | _, _ => None
        end
    | _, _ => None
    end
  else if is_bit_slice_fn f "get_mut" then
    Some match vs with
         | [x; r] =>
             match view_of x, range_of r with
             | Some s, Some (start, stop) =>
                 if Nat.leb start stop && Nat.leb stop (sv_len s)
                 then returned (some_value (view_value (sub_view s start stop)))
                 else returned none_value
             | _, _ => fail "BitSlice::get_mut with unexpected arguments"
             end
         | _ => fail "BitSlice::get_mut with unexpected arguments"
         end
  else if is_bit_slice_fn f "fill" then
    Some match vs with
         | [x; VBool b] =>
             with_view vs (fun s =>
               ws <- read_view env s ;;
               write_view env s (fill_bits ws (sv_head s) (sv_len s) b) ;;;
               returned VUnit)
         | _ => fail "BitSlice::fill with unexpected arguments"
         end
  else if is_bit_slice_fn f "set" then
    Some match vs with
         | [x; VBits _ i; VBool b] =>
             with_view vs (fun s =>
               if Nat.leb (sv_len s) (Z.to_nat i) then panics
               else ws <- read_view env s ;;
                    write_view env s (with_bit ws (sv_head s + Z.to_nat i) b) ;;;
                    returned VUnit)
         | _ => fail "BitSlice::set with unexpected arguments"
         end
  else if is_bit_slice_fn f "first_one" then
    Some (with_view vs (fun s =>
      ws <- read_view env s ;;
      match first_one_bits ws (sv_head s) (sv_len s) with
      | Some i => returned (some_value (VBits WSize (Z.of_nat i)))
      | None => returned none_value
      end))
  else if is_bit_slice_fn f "count_ones" then
    Some (with_view vs (fun s =>
      ws <- read_view env s ;;
      returned (VBits WSize (Z.of_nat (count_ones_bits ws (sv_head s) (sv_len s))))))
  else if is_bit_slice_fn f "all" then
    Some (with_view vs (fun s =>
      ws <- read_view env s ;;
      returned (VBool (all_bits ws (sv_head s) (sv_len s)))))
  else if is_bit_slice_fn f "not_all" then
    Some (with_view vs (fun s =>
      ws <- read_view env s ;;
      returned (VBool (negb (all_bits ws (sv_head s) (sv_len s))))))
  else None.

End Models.

From RustRocq Require Import Syntax Subst LayoutAlg.
From Stdlib Require Import Bool List String ZArith.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope list_scope.

Notation length := List.length.

Section Values.

  Inductive pointer_provenance :=
    | ProvenanceNone
    | ProvenanceAllocation (allocation : nat)
    | ProvenanceFunction (definition : string)
    | ProvenanceVTable (concrete : ty).

  Inductive pointer_metadata :=
    | PointerThin
    | PointerLength (length : nat)
    | PointerVTable (concrete : ty).

  Record pointer_value := PointerValue {
    pointer_provenance_of : pointer_provenance;
    pointer_address : Z;
    pointer_metadata_of : pointer_metadata;
  }.

  Inductive runtime_value :=
    | VUnit
    | VBool (value : bool)
    | VChar (value : Z)
    | VBits (width : int_width) (bits : Z)
    | VPtr (pointer : pointer_value)
    | VArray (elements : list runtime_value)
    | VTuple (fields : list runtime_value)
    | VAdt (declaration : string) (variant : nat) (fields : list runtime_value).

  Definition VPointer (allocation offset : nat) : runtime_value :=
    VPtr (PointerValue (ProvenanceAllocation allocation) (Z.of_nat offset) PointerThin).

End Values.

Section Results.

  Inductive ub_reason :=
    | UbInvalidPointerProvenance
    | UbDanglingPointer
    | UbOutOfBounds
    | UbMisaligned
    | UbUseAfterFree
    | UbReadUninitialized
    | UbReadDead
    | UbInvalidScalar
    | UbInvalidEnumTag
    | UbInvalidMetadata
    | UbReachedUnreachable
    | UbDivisionByZero
    | UbDivisionOverflow.

  Inductive access_result (A : Type) :=
    | AccessOk (a : A)
    | AccessUb (reason : ub_reason)
    | AccessFail.

  #[global] Arguments AccessOk {A} _.
  #[global] Arguments AccessUb {A} _.
  #[global] Arguments AccessFail {A}.

  Definition and_then {A B} (r : access_result A) (k : A -> access_result B) : access_result B :=
    match r with
    | AccessOk a => k a
    | AccessUb u => AccessUb u
    | AccessFail => AccessFail
    end.

  Definition required {A} (o : option A) : access_result A :=
    match o with Some a => AccessOk a | None => AccessFail end.

  Definition ub_unless (b : bool) (reason : ub_reason) : access_result unit :=
    if b then AccessOk tt else AccessUb reason.

  Fixpoint all_ok {A} (rs : list (access_result A)) : access_result (list A) :=
    match rs with
    | [] => AccessOk []
    | r :: rest => and_then r (fun a => and_then (all_ok rest) (fun xs => AccessOk (a :: xs)))
    end.

  Fixpoint all_some {A} (os : list (option A)) : option (list A) :=
    match os with
    | [] => Some []
    | Some a :: rest => option_map (cons a) (all_some rest)
    | None :: _ => None
    end.

  Fixpoint set_nth {A : Type} (index : nat) (value : A) (values : list A) : option (list A) :=
    match index, values with
    | O, _ :: rest => Some (value :: rest)
    | S index, v :: rest => option_map (cons v) (set_nth index value rest)
    | _, [] => None
    end.

End Results.

Notation "x <-? r ;; k" := (and_then r (fun x => k))
  (at level 61, r at next level, right associativity).

Section Bytes.

  Inductive mbyte :=
    | MUninit
    | MByte (value : Z) (provenance : option pointer_provenance).

  Fixpoint little_endian (n : nat) (z : Z) : list Z :=
    match n with
    | O => []
    | S n => Z.modulo z 256 :: little_endian n (Z.div z 256)
    end.

  Fixpoint from_little_endian (bs : list Z) : Z :=
    match bs with
    | [] => 0
    | b :: rest => b + 256 * from_little_endian rest
    end.

  Definition int_bytes (n : nat) (z : Z) (provenance : option pointer_provenance) : list mbyte :=
    map (fun b => MByte b provenance) (little_endian n z).

  Fixpoint byte_values (bs : list mbyte) : option (list Z) :=
    match bs with
    | [] => Some []
    | MByte b _ :: rest => option_map (cons b) (byte_values rest)
    | MUninit :: _ => None
    end.

  Definition int_value (bs : list mbyte) : access_result Z :=
    match byte_values bs with
    | Some zs => AccessOk (from_little_endian zs)
    | None => AccessUb UbReadUninitialized
    end.

  Definition bytes_at (offset size : nat) (bs : list mbyte) : list mbyte :=
    firstn size (skipn offset bs).

  Definition splice (offset : nat) (part whole : list mbyte) : list mbyte :=
    firstn offset whole ++ part ++ skipn (offset + length part) whole.

  Definition provenance_eqb (a b : pointer_provenance) : bool :=
    match a, b with
    | ProvenanceNone, ProvenanceNone => true
    | ProvenanceAllocation x, ProvenanceAllocation y => Nat.eqb x y
    | ProvenanceFunction x, ProvenanceFunction y => String.eqb x y
    | ProvenanceVTable x, ProvenanceVTable y => ty_eqb x y
    | _, _ => false
    end.

  Definition byte_provenance (b : mbyte) : pointer_provenance :=
    match b with
    | MByte _ (Some p) => p
    | _ => ProvenanceNone
    end.

  Definition common_provenance (bs : list mbyte) : pointer_provenance :=
    match bs with
    | b :: rest =>
        let p := byte_provenance b in
        if forallb (fun c => provenance_eqb p (byte_provenance c)) rest then p else ProvenanceNone
    | [] => ProvenanceNone
    end.

End Bytes.

Section Layouts.

  Inductive pointer_kind := Thin | WithLength | WithVTable.

  Inductive layout :=
    | LInt (width : int_width)
    | LBool
    | LChar
    | LRawPtr (kind : pointer_kind)
    | LRef (pointee : ty) (kind : pointer_kind)
    | LUnit
    | LNever
    | LArray (element : layout) (count : nat)
    | LStruct (declaration : option name) (size align : nat) (fields : list (nat * layout))
    | LEnum (declaration : name) (size align tag_offset tag_size : nat) (variants : list layout).

  Definition int_width_bytes (w : int_width) : nat :=
    match w with
    | W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8 | W128 => 16 | WSize => 8
    end.

  Definition pointer_bytes : nat := 8.

  Definition pointer_size (kind : pointer_kind) : nat :=
    match kind with
    | Thin => pointer_bytes
    | WithLength | WithVTable => 2 * pointer_bytes
    end.

  Fixpoint size_of (l : layout) : nat :=
    match l with
    | LInt w => int_width_bytes w
    | LBool => 1
    | LChar => 4
    | LRawPtr kind | LRef _ kind => pointer_size kind
    | LUnit | LNever => 0
    | LArray e n => n * size_of e
    | LStruct _ size _ _ | LEnum _ size _ _ _ _ => size
    end.

  Fixpoint align_of (l : layout) : nat :=
    match l with
    | LInt w => int_width_bytes w
    | LBool => 1
    | LChar => 4
    | LRawPtr _ | LRef _ _ => pointer_bytes
    | LUnit | LNever => 1
    | LArray e _ => align_of e
    | LStruct _ _ align _ | LEnum _ _ align _ _ _ => align
    end.

End Layouts.

Section Encoding.

  Definition width_limit (w : int_width) : Z := 2 ^ Z.of_nat (8 * int_width_bytes w).

  Definition valid_char (z : Z) : bool :=
    (0 <=? z)%Z && (z <=? 1114111)%Z && negb ((55296 <=? z)%Z && (z <=? 57343)%Z).

  Definition encode_pointer (kind : pointer_kind) (p : pointer_value) : option (list mbyte) :=
    let address := int_bytes pointer_bytes (Z.modulo (pointer_address p) (2 ^ 64))
                     (Some (pointer_provenance_of p)) in
    match kind, pointer_metadata_of p with
    | Thin, PointerThin => Some address
    | WithLength, PointerLength n => Some (address ++ int_bytes pointer_bytes (Z.of_nat n) None)
    | WithVTable, PointerVTable t =>
        Some (address ++ int_bytes pointer_bytes 0 (Some (ProvenanceVTable t)))
    | _, _ => None
    end.

  Definition decode_pointer (kind : pointer_kind) (bs : list mbyte) : access_result pointer_value :=
    let address_bytes := firstn pointer_bytes bs in
    let metadata_bytes := skipn pointer_bytes bs in
    address <-? int_value address_bytes ;;
    let pointer := PointerValue (common_provenance address_bytes) address in
    match kind with
    | Thin => AccessOk (pointer PointerThin)
    | WithLength =>
        n <-? int_value metadata_bytes ;;
        AccessOk (pointer (PointerLength (Z.to_nat n)))
    | WithVTable =>
        _ <-? int_value metadata_bytes ;;
        match common_provenance metadata_bytes with
        | ProvenanceVTable t => AccessOk (pointer (PointerVTable t))
        | _ => AccessUb UbInvalidMetadata
        end
    end.

  Definition struct_fields (declaration : option name) (v : runtime_value)
      : option (list runtime_value) :=
    match declaration, v with
    | None, VTuple vs => Some vs
    | None, VUnit => Some []
    | Some d, VAdt d' 0 vs => if String.eqb d d' then Some vs else None
    | _, _ => None
    end.

  Fixpoint place_fields (fields : list (nat * (runtime_value -> option (list mbyte))))
      (vs : list runtime_value) (bytes : list mbyte) : option (list mbyte) :=
    match fields, vs with
    | [], [] => Some bytes
    | (offset, encode_field) :: fields, v :: vs =>
        match encode_field v with
        | Some part => place_fields fields vs (splice offset part bytes)
        | None => None
        end
    | _, _ => None
    end.

  Fixpoint encode (l : layout) : runtime_value -> option (list mbyte) :=
    match l with
    | LInt w => fun v =>
        match v with
        | VBits w' z =>
            if int_width_eqb w w' && (0 <=? z)%Z && (z <? width_limit w)%Z
            then Some (int_bytes (int_width_bytes w) z None) else None
        | _ => None
        end
    | LBool => fun v =>
        match v with
        | VBool b => Some [MByte (if b then 1 else 0)%Z None]
        | _ => None
        end
    | LChar => fun v =>
        match v with
        | VChar z => if valid_char z then Some (int_bytes 4 z None) else None
        | _ => None
        end
    | LRawPtr kind | LRef _ kind => fun v =>
        match v with
        | VPtr p => encode_pointer kind p
        | _ => None
        end
    | LUnit => fun v =>
        match struct_fields None v with
        | Some [] => Some []
        | _ => None
        end
    | LNever => fun _ => None
    | LArray e n =>
        let encode_element := encode e in
        fun v =>
          match v with
          | VArray vs =>
              if Nat.eqb (length vs) n
              then option_map (@List.concat _) (all_some (map encode_element vs)) else None
          | _ => None
          end
    | LStruct declaration size _ fields =>
        let encoders := map (fun '(offset, f) => (offset, encode f)) fields in
        fun v =>
          match struct_fields declaration v with
          | Some vs => place_fields encoders vs (repeat MUninit size)
          | None => None
          end
    | LEnum declaration _ _ tag_offset tag_size variants =>
        let encoders := map encode variants in
        fun v =>
          match v with
          | VAdt d k vs =>
              match String.eqb declaration d, nth_error encoders k with
              | true, Some encode_variant =>
                  option_map (splice tag_offset (int_bytes tag_size (Z.of_nat k) None))
                    (encode_variant (VTuple vs))
              | _, _ => None
              end
          | _ => None
          end
    end.

  Definition chunks (size count : nat) (bs : list mbyte) : list (list mbyte) :=
    map (fun i => bytes_at (i * size) size bs) (seq 0 count).

  Fixpoint decode (l : layout) : list mbyte -> access_result runtime_value :=
    match l with
    | LInt w => fun bs => z <-? int_value bs ;; AccessOk (VBits w z)
    | LBool => fun bs =>
        z <-? int_value bs ;;
        if Z.eqb z 0 then AccessOk (VBool false)
        else if Z.eqb z 1 then AccessOk (VBool true)
        else AccessUb UbInvalidScalar
    | LChar => fun bs =>
        z <-? int_value bs ;;
        _ <-? ub_unless (valid_char z) UbInvalidScalar ;;
        AccessOk (VChar z)
    | LRawPtr kind | LRef _ kind => fun bs => p <-? decode_pointer kind bs ;; AccessOk (VPtr p)
    | LUnit => fun _ => AccessOk VUnit
    | LNever => fun _ => AccessUb UbInvalidScalar
    | LArray e n =>
        let decode_element := decode e in
        fun bs =>
          vs <-? all_ok (map decode_element (chunks (size_of e) n bs)) ;;
          AccessOk (VArray vs)
    | LStruct declaration _ _ fields =>
        let decoders := map (fun '(offset, f) bs => decode f (bytes_at offset (size_of f) bs))
                            fields in
        fun bs =>
          vs <-? all_ok (map (fun decode_field => decode_field bs) decoders) ;;
          match declaration with
          | None => AccessOk (VTuple vs)
          | Some d => AccessOk (VAdt d 0 vs)
          end
    | LEnum declaration _ _ tag_offset tag_size variants =>
        let decoders := map decode variants in
        fun bs =>
          tag <-? int_value (bytes_at tag_offset tag_size bs) ;;
          let k := Z.to_nat tag in
          match nth_error decoders k with
          | Some decode_variant =>
              v <-? decode_variant bs ;;
              match v with
              | VTuple vs => AccessOk (VAdt declaration k vs)
              | _ => AccessFail
              end
          | None => AccessUb UbInvalidEnumTag
          end
    end.

End Encoding.

Section Memory.

  Record allocation := AllocationData {
    allocation_size : nat;
    allocation_align : nat;
    allocation_bytes : list mbyte;
    allocation_live : bool;
  }.

  Definition memory_state := list allocation.

  Definition live_allocation (m : memory_state) (a : nat) : access_result allocation :=
    match nth_error m a with
    | Some al => if allocation_live al then AccessOk al else AccessUb UbUseAfterFree
    | None => AccessUb UbDanglingPointer
    end.

  Definition check_range (al : allocation) (offset size align : nat) : access_result unit :=
    _ <-? ub_unless (Nat.leb (offset + size) (allocation_size al)) UbOutOfBounds ;;
    ub_unless (Nat.leb align (allocation_align al) && Nat.eqb (Nat.modulo offset align) 0)
      UbMisaligned.

  Definition load (m : memory_state) (a offset size align : nat) : access_result (list mbyte) :=
    al <-? live_allocation m a ;;
    _ <-? check_range al offset size align ;;
    AccessOk (bytes_at offset size (allocation_bytes al)).

  Definition with_bytes (al : allocation) (bs : list mbyte) : allocation :=
    AllocationData (allocation_size al) (allocation_align al) bs (allocation_live al).

  Definition store (m : memory_state) (a offset : nat) (bs : list mbyte) (align : nat)
      : access_result memory_state :=
    al <-? live_allocation m a ;;
    _ <-? check_range al offset (length bs) align ;;
    required (set_nth a (with_bytes al (splice offset bs (allocation_bytes al))) m).

  Definition kill_allocation (m : memory_state) (a : nat) : option memory_state :=
    match nth_error m a with
    | Some al =>
        set_nth a (AllocationData (allocation_size al) (allocation_align al)
                     (repeat MUninit (allocation_size al)) false) m
    | None => None
    end.

End Memory.

Section UnsizedTypes.

  Definition is_phantom (t : ty) : bool :=
    match t with
    | TAdt p _ =>
        String.eqb p "core::marker::PhantomData" || String.eqb p "std::marker::PhantomData"
    | _ => false
    end.

  Definition transparent_tail (adts : list adt_def) (path : name) (args : list garg) : option ty :=
    match find_adt adts path with
    | Some a =>
        if existsb (String.eqb "transparent") (ad_repr a) then
          match ad_kind a, ad_variants a with
          | AkStruct, [v] =>
              match rev (variant_field_tys args v) with
              | TSlice e :: rest => if forallb is_phantom rest then Some (TSlice e) else None
              | TStr :: rest => if forallb is_phantom rest then Some TStr else None
              | _ => None
              end
          | _, _ => None
          end
        else None
    | None => None
    end.

  Definition unsized_view (adts : list adt_def) (t : ty) : ty :=
    match t with
    | TAdt p args =>
        match transparent_tail adts p args with
        | Some tail => tail
        | None => t
        end
    | _ => t
    end.

  Definition pointer_kind_to (adts : list adt_def) (pointee : ty) : pointer_kind :=
    match unsized_view adts pointee with
    | TSlice _ | TStr => WithLength
    | TDynamic _ _ => WithVTable
    | _ => Thin
    end.

  Definition const_nat (c : tconst) : option nat :=
    match c with
    | CValue _ z => if Z.leb 0 z then Some (Z.to_nat z) else None
    | _ => None
    end.

End UnsizedTypes.

Section LayoutOfTypes.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition size_align_of (l : layout) : size_align := (size_of l, align_of l).

  Definition struct_layout (declaration : option name) (alg_name : name) (reprs : list repr)
      (fields : list layout) : option layout :=
    match struct_alg alg_name (map size_align_of fields) reprs with
    | Some a => Some (LStruct declaration (ag_size a) (ag_align a) (combine (ag_offsets a) fields))
    | None => None
    end.

  Definition enum_layout_of (declaration : name) (reprs : list repr) (variants : list (list layout))
      : option layout :=
    match enum_alg declaration (map (map size_align_of) variants) reprs with
    | Some e =>
        let variant_struct '(placed, fields) :=
          LStruct None (en_size e) (en_align e) (combine (ag_offsets placed) fields) in
        Some (LEnum declaration (en_size e) (en_align e) (en_tag_offset e) (scalar_bytes (en_tag e))
                (map variant_struct (combine (en_variants e) variants)))
    | None => None
    end.

  Fixpoint layout_of_fuel (fuel : nat) (t : ty) : option layout :=
    match fuel with
    | O => None
    | S fuel =>
        let layouts ts := all_some (map (layout_of_fuel fuel) ts) in
        match t with
        | TBool => Some LBool
        | TChar => Some LChar
        | TInt w | TUint w => Some (LInt w)
        | TRef _ pointee _ => Some (LRef pointee (pointer_kind_to adts pointee))
        | TRawPtr pointee _ => Some (LRawPtr (pointer_kind_to adts pointee))
        | TFnPtr _ => Some (LRawPtr Thin)
        | TFnDef _ _ | TTuple [] => Some LUnit
        | TNever => Some LNever
        | TPat base _ => layout_of_fuel fuel base
        | TArray e n =>
            match layout_of_fuel fuel e, const_nat n with
            | Some l, Some k => Some (LArray l k)
            | _, _ => None
            end
        | TTuple ts =>
            match layouts ts with
            | Some fields => struct_layout None "" [] fields
            | None => None
            end
        | TClosure _ args =>
            match closure_upvars args with
            | Some upvars => layout_of_fuel fuel upvars
            | None => None
            end
        | TAdt path args =>
            match find_adt adts path with
            | Some d =>
                let reprs := reprs_of (ad_repr d) in
                let fields_of v := layouts (variant_field_tys args v) in
                match ad_kind d, ad_variants d with
                | AkStruct, [v] =>
                    match fields_of v with
                    | Some fields => struct_layout (Some path) path reprs fields
                    | None => None
                    end
                | AkEnum, vs =>
                    match all_some (map fields_of vs) with
                    | Some variants => enum_layout_of path reprs variants
                    | None => None
                    end
                | _, _ => None
                end
            | None => None
            end
        | _ => None
        end
    end.

  Definition layout_of (t : ty) : option layout := layout_of_fuel 64 t.

  Definition extent (t : ty) (meta : pointer_metadata) : option (nat * nat) :=
    match unsized_view adts t, meta with
    | TSlice e, PointerLength n =>
        option_map (fun l => (n * size_of l, align_of l)) (layout_of e)
    | TStr, PointerLength n => Some (n, 1)
    | TDynamic _ _, PointerVTable _ => Some (0, 1)
    | TSlice _, _ | TStr, _ | TDynamic _ _, _ => None
    | _, PointerThin => option_map size_align_of (layout_of t)
    | _, _ => None
    end.

  Definition encodable (t : ty) (v : runtime_value) : bool :=
    match layout_of t with
    | Some l => match encode l v with Some _ => true | None => false end
    | None => false
    end.

End LayoutOfTypes.

Section References.

  Context `{Alg : LayoutAlg} (adts : list adt_def) (m : memory_state).

  Definition valid_reference (pointee : ty) (p : pointer_value) : access_result unit :=
    match extent adts pointee (pointer_metadata_of p) with
    | None => AccessUb UbInvalidMetadata
    | Some (size, align) =>
        let address := pointer_address p in
        match pointer_provenance_of p with
        | ProvenanceAllocation a =>
            _ <-? ub_unless (0 <=? address)%Z UbOutOfBounds ;;
            if Nat.eqb size 0
            then ub_unless (Nat.eqb (Nat.modulo (Z.to_nat address) align) 0) UbMisaligned
            else al <-? live_allocation m a ;; check_range al (Z.to_nat address) size align
        | _ =>
            ub_unless (Nat.eqb size 0 && negb (Z.eqb address 0)
                       && Z.eqb (Z.modulo address (Z.of_nat align)) 0)
              UbDanglingPointer
        end
    end.

  Fixpoint check_all (checks : list (runtime_value -> access_result unit))
      (vs : list runtime_value) : access_result unit :=
    match checks, vs with
    | check :: checks, v :: vs => _ <-? check v ;; check_all checks vs
    | _, _ => AccessOk tt
    end.

  Fixpoint references_valid (l : layout) : runtime_value -> access_result unit :=
    match l with
    | LRef pointee _ => fun v =>
        match v with
        | VPtr p => valid_reference pointee p
        | _ => AccessOk tt
        end
    | LArray e _ =>
        let check_element := references_valid e in
        fun v =>
          match v with
          | VArray vs => check_all (repeat check_element (length vs)) vs
          | _ => AccessOk tt
          end
    | LStruct _ _ _ fields =>
        let checks := map (fun '(_, f) => references_valid f) fields in
        fun v =>
          match v with
          | VTuple vs | VAdt _ _ vs => check_all checks vs
          | _ => AccessOk tt
          end
    | LEnum _ _ _ _ _ variants =>
        let checks := map references_valid variants in
        fun v =>
          match v with
          | VAdt _ k vs =>
              match nth_error checks k with
              | Some check_variant => check_variant (VTuple vs)
              | None => AccessOk tt
              end
          | _ => AccessOk tt
          end
    | _ => fun _ => AccessOk tt
    end.

End References.

Section Places.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Record location := Location {
    loc_allocation : nat;
    loc_offset : nat;
    loc_ty : ty;
    loc_metadata : pointer_metadata;
    loc_variant : option nat;
  }.

  Definition inner (l : location) (offset : nat) (t : ty) (meta : pointer_metadata) : location :=
    Location (loc_allocation l) (loc_offset l + offset) t meta None.

  Definition retyped (l : location) (t : ty) : location :=
    Location (loc_allocation l) (loc_offset l) t (loc_metadata l) (loc_variant l).

  Definition in_variant (l : location) (k : nat) : location :=
    Location (loc_allocation l) (loc_offset l) (loc_ty l) (loc_metadata l) (Some k).

  Definition located_layout (l : location) : access_result layout :=
    required (layout_of adts (loc_ty l)).

  Definition load_value (m : memory_state) (l : location) : access_result runtime_value :=
    lay <-? located_layout l ;;
    bs <-? load m (loc_allocation l) (loc_offset l) (size_of lay) (align_of lay) ;;
    v <-? decode lay bs ;;
    _ <-? references_valid adts m lay v ;;
    AccessOk v.

  Definition store_value (m : memory_state) (l : location) (v : runtime_value)
      : access_result memory_state :=
    lay <-? located_layout l ;;
    bs <-? required (encode lay v) ;;
    _ <-? references_valid adts m lay v ;;
    store m (loc_allocation l) (loc_offset l) bs (align_of lay).

  Definition located_extent (l : location) : access_result (nat * nat) :=
    required (extent adts (loc_ty l) (loc_metadata l)).

  Definition pointer_target (t : ty) (p : pointer_value) : access_result location :=
    match pointer_provenance_of p with
    | ProvenanceAllocation a =>
        _ <-? ub_unless (0 <=? pointer_address p)%Z UbOutOfBounds ;;
        AccessOk (Location a (Z.to_nat (pointer_address p)) t (pointer_metadata_of p) None)
    | _ => AccessUb UbInvalidPointerProvenance
    end.

  Definition element_ty (t : ty) : option ty :=
    match unsized_view adts t with
    | TArray e _ | TSlice e => Some e
    | _ => None
    end.

  Definition element_count (l : location) : option nat :=
    match unsized_view adts (loc_ty l), loc_metadata l with
    | TArray _ n, _ => const_nat n
    | TSlice _, PointerLength n => Some n
    | _, _ => None
    end.

  Definition field_offset (lay : layout) (variant : option nat) (i : nat) : option nat :=
    let offset_in fields := option_map fst (nth_error fields i) in
    match lay, variant with
    | LStruct _ _ _ fields, _ => offset_in fields
    | LEnum _ _ _ _ _ variants, Some k =>
        match nth_error variants k with
        | Some (LStruct _ _ _ fields) => offset_in fields
        | _ => None
        end
    | _, _ => None
    end.

  Definition element_at (l : location) (i : nat) : access_result location :=
    n <-? required (element_count l) ;;
    e <-? required (element_ty (loc_ty l)) ;;
    lay <-? required (layout_of adts e) ;;
    _ <-? ub_unless (Nat.ltb i n) UbOutOfBounds ;;
    AccessOk (inner l (i * size_of lay) e PointerThin).

  Definition subslice_at (l : location) (from stop : nat) : access_result location :=
    n <-? required (element_count l) ;;
    e <-? required (element_ty (loc_ty l)) ;;
    lay <-? required (layout_of adts e) ;;
    _ <-? ub_unless (Nat.leb from stop && Nat.leb stop n) UbOutOfBounds ;;
    let offset := from * size_of lay in
    match unsized_view adts (loc_ty l) with
    | TArray _ _ =>
        AccessOk (inner l offset (TArray e (CValue (TUint WSize) (Z.of_nat (stop - from))))
                    PointerThin)
    | _ => AccessOk (inner l offset (TSlice e) (PointerLength (stop - from)))
    end.

  Definition variant_tag (m : memory_state) (l : location) : access_result (option nat) :=
    lay <-? located_layout l ;;
    match lay with
    | LEnum _ _ _ tag_offset tag_size _ =>
        bs <-? load m (loc_allocation l) (loc_offset l + tag_offset) tag_size 1 ;;
        tag <-? int_value bs ;;
        AccessOk (Some (Z.to_nat tag))
    | _ => AccessOk None
    end.

  Definition project (m : memory_state) (index_value : local -> access_result nat)
      (l : location) (pe : proj_elem) : access_result location :=
    match pe with
    | PDeref =>
        match loc_ty l with
        | TRef _ pointee _ | TRawPtr pointee _ =>
            v <-? load_value m l ;;
            match v with
            | VPtr p =>
                target <-? pointer_target pointee p ;;
                _ <-? live_allocation m (loc_allocation target) ;;
                AccessOk target
            | _ => AccessFail
            end
        | _ => AccessFail
        end
    | PField i t =>
        lay <-? located_layout l ;;
        offset <-? required (field_offset lay (loc_variant l) i) ;;
        AccessOk (inner l offset t PointerThin)
    | PDowncast _ k =>
        tag <-? variant_tag m l ;;
        match tag with
        | Some k' => _ <-? ub_unless (Nat.eqb k k') UbInvalidEnumTag ;; AccessOk (in_variant l k)
        | None => AccessOk (in_variant l k)
        end
    | PIndex i => n <-? index_value i ;; element_at l n
    | PConstantIndex offset _ from_end =>
        n <-? required (element_count l) ;;
        element_at l (if from_end then n - offset else offset)
    | PSubslice from to from_end =>
        n <-? required (element_count l) ;;
        subslice_at l from (if from_end then n - to else to)
    | POpaqueCast t | PUnwrapUnsafeBinder t => AccessOk (retyped l t)
    end.

End Places.

Section Frames.

  Inductive local_storage :=
    | LocalDead
    | LocalUnallocated
    | LocalAllocated (allocation : nat).

  Record prog_state := ByteState {
    state_locals : list local_storage;
    state_memory : memory_state;
  }.

  Definition state_with_locals (st : prog_state) (locals : list local_storage) : prog_state :=
    ByteState locals (state_memory st).

  Definition state_with_memory (st : prog_state) (memory : memory_state) : prog_state :=
    ByteState (state_locals st) memory.

  Context `{Alg : LayoutAlg} (adts : list adt_def) (local_tys : list ty).

  Definition local_location (st : prog_state) (x : local) : access_result location :=
    match nth_error (state_locals st) x, nth_error local_tys x with
    | Some (LocalAllocated a), Some t =>
        _ <-? live_allocation (state_memory st) a ;;
        AccessOk (Location a 0 t PointerThin None)
    | Some LocalDead, _ => AccessUb UbReadDead
    | Some LocalUnallocated, Some t =>
        match layout_of adts t with
        | Some _ => AccessUb UbReadUninitialized
        | None => AccessFail
        end
    | _, _ => AccessFail
    end.

  Definition index_value (st : prog_state) (x : local) : access_result nat :=
    l <-? local_location st x ;;
    v <-? load_value adts (state_memory st) (retyped l (TUint WSize)) ;;
    match v with
    | VBits _ z => AccessOk (Z.to_nat z)
    | _ => AccessFail
    end.

  Definition locate (st : prog_state) (p : place) : access_result location :=
    start <-? local_location st (pl_local p) ;;
    fold_left (fun acc pe => l <-? acc ;; project adts (state_memory st) (index_value st) l pe)
      (pl_proj p) (AccessOk start).

  Definition read_place (st : prog_state) (p : place) : access_result runtime_value :=
    l <-? locate st p ;;
    load_value adts (state_memory st) l.

  Definition write_place (st : prog_state) (p : place) (v : runtime_value)
      : access_result prog_state :=
    l <-? locate st p ;;
    m <-? store_value adts (state_memory st) l v ;;
    AccessOk (state_with_memory st m).

  Definition address_of_place (st : prog_state) (p : place) : access_result runtime_value :=
    l <-? locate st p ;;
    AccessOk (VPtr (PointerValue (ProvenanceAllocation (loc_allocation l))
                      (Z.of_nat (loc_offset l)) (loc_metadata l))).

  Definition deinit_place (st : prog_state) (p : place) : access_result prog_state :=
    l <-? locate st p ;;
    e <-? located_extent adts l ;;
    m <-? store (state_memory st) (loc_allocation l) (loc_offset l) (repeat MUninit (fst e)) 1 ;;
    AccessOk (state_with_memory st m).

  Definition place_initialized (st : prog_state) (p : place) : access_result bool :=
    l <-? locate st p ;;
    e <-? located_extent adts l ;;
    bs <-? load (state_memory st) (loc_allocation l) (loc_offset l) (fst e) 1 ;;
    AccessOk (existsb (fun b => match b with MByte _ _ => true | MUninit => false end) bs).

End Frames.

Section Pointers.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition read_pointer (m : memory_state) (t : ty) (p : pointer_value)
      : access_result runtime_value :=
    l <-? pointer_target t p ;; load_value adts m l.

  Definition write_pointer (m : memory_state) (t : ty) (p : pointer_value) (v : runtime_value)
      : access_result memory_state :=
    l <-? pointer_target t p ;; store_value adts m l v.

End Pointers.

Section Allocation.

  Context `{Alg : LayoutAlg} (adts : list adt_def).

  Definition allocate (m : memory_state) (l : layout) (bs : list mbyte) : nat * memory_state :=
    (length m, m ++ [AllocationData (size_of l) (align_of l) bs true]).

  Definition allocate_value (m : memory_state) (t : ty) (v : runtime_value)
      : option (nat * memory_state) :=
    match layout_of adts t with
    | Some l => option_map (allocate m l) (encode l v)
    | None => None
    end.

  Definition allocate_uninit (m : memory_state) (t : ty) : option (nat * memory_state) :=
    option_map (fun l => allocate m l (repeat MUninit (size_of l))) (layout_of adts t).

  Definition release_local (st : prog_state) (x : local) : memory_state :=
    match nth_error (state_locals st) x with
    | Some (LocalAllocated a) =>
        match kill_allocation (state_memory st) a with
        | Some m => m
        | None => state_memory st
        end
    | _ => state_memory st
    end.

  Definition storage_live (local_tys : list ty) (st : prog_state) (x : local)
      : option prog_state :=
    match nth_error local_tys x with
    | Some t =>
        match allocate_uninit (release_local st x) t with
        | Some (a, m) =>
            option_map (fun locals => ByteState locals m)
              (set_nth x (LocalAllocated a) (state_locals st))
        | None => None
        end
    | None => None
    end.

  Definition storage_dead (st : prog_state) (x : local) : option prog_state :=
    option_map (fun locals => ByteState locals (release_local st x))
      (set_nth x LocalDead (state_locals st)).

  Inductive slot := Dead | Uninit | Init (t : ty) (value : runtime_value).

  Fixpoint allocate_slots (slots : list slot) (m : memory_state)
      : list local_storage * memory_state :=
    match slots with
    | [] => ([], m)
    | s :: rest =>
        let '(storage, m1) :=
          match s with
          | Dead => (LocalDead, m)
          | Uninit => (LocalUnallocated, m)
          | Init t v =>
              match allocate_value m t v with
              | Some (a, m1) => (LocalAllocated a, m1)
              | None => (LocalUnallocated, m)
              end
          end in
        let '(storages, m2) := allocate_slots rest m1 in
        (storage :: storages, m2)
    end.

  Definition local_state (slots : list slot) : prog_state :=
    let '(locals, m) := allocate_slots slots [] in ByteState locals m.

End Allocation.

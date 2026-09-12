From RustRocq Require Import Syntax Layout.
From Stdlib Require Import Bool Lia List String ZArith.

Import ListNotations.

Open Scope list_scope.
Notation length := List.length.
Open Scope bool_scope.
Open Scope Z_scope.

Definition float_width_bits (w : float_width) : nat :=
  match w with FW16 => 16%nat | FW32 => 32%nat | FW64 => 64%nat | FW128 => 128%nat end.

Definition const_nat (c : tconst) : option nat :=
  match c with
  | CValue _ bits => if Z.leb 0 bits then Some (Z.to_nat bits) else None
  | _ => None
  end.

Inductive value_shape :=
  | ShapeUnit
  | ShapeNever
  | ShapeBool
  | ShapeChar
  | ShapeFloat (bits : nat)
  | ShapeBits (width : int_width)
  | ShapePointer (pointee : value_shape)
  | ShapeReference (kind : mutability) (pointee : value_shape)
  | ShapeRawPointer (kind : mutability) (pointee : value_shape)
  | ShapeArray (element : value_shape) (length : nat)
  | ShapeSlice (element : value_shape)
  | ShapeStr
  | ShapeTuple (fields : list value_shape)
  | ShapeAdtType (t : ty)
  | ShapeAdt (declaration : string) (variant : nat)
      (fields : list value_shape).

Inductive pointer_provenance :=
  | ProvenanceNone
  | ProvenanceAllocation (allocation : nat)
  | ProvenanceExposed (allocations : list nat)
  | ProvenanceFunction (definition : string).

Inductive pointer_metadata :=
  | PointerThin
  | PointerLength (length : nat)
  | PointerVTable
      (provenance : pointer_provenance)
      (address : Z).

Record pointer_value := PointerValue {
  pointer_provenance_of : pointer_provenance;
  pointer_address : Z;
  pointer_metadata_of : pointer_metadata;
}.

Definition byte := Z.

Inductive runtime_value :=
  | VUnit
  | VBool (value : bool)
  | VChar (value : Z)
  | VFloatBits (width : nat) (bits : Z)
  | VBits (width : int_width) (bits : Z)
  | VPointerValue (pointee : value_shape) (pointer : pointer_value)
  | VFunction (definition : string)
  | VArray (element : value_shape) (fields : list runtime_value)
  | VTuple (fields : list runtime_value)
  | VAdt (declaration : string) (variant : nat) (fields : list runtime_value)
  | VUnion (declaration : string) (active_field : nat)
      (field : runtime_value)
  | VRawAggregate (shape : value_shape)
      (bytes : list byte) (init : list bool)
      (provenance : list (option pointer_provenance)).

Definition VPointer (pointee : value_shape) (allocation offset : nat)
    : runtime_value :=
  VPointerValue pointee
    (PointerValue (ProvenanceAllocation allocation) (Z.of_nat offset)
      PointerThin).

Definition VPointerWithoutProvenance (pointee : value_shape) (address : Z)
    : runtime_value :=
  VPointerValue pointee (PointerValue ProvenanceNone address PointerThin).

Definition pointer_allocation_offset (pointer : pointer_value)
    : option (nat * nat) :=
  match pointer_provenance_of pointer with
  | ProvenanceAllocation allocation =>
      if 0 <=? pointer_address pointer then
        Some (allocation, Z.to_nat (pointer_address pointer))
      else None
  | ProvenanceNone | ProvenanceExposed _ | ProvenanceFunction _ => None
  end.

Definition pointer_length (pointer : pointer_value) : option nat :=
  match pointer_metadata_of pointer with
  | PointerLength length => Some length
  | PointerThin | PointerVTable _ _ => None
  end.

Inductive slot := Dead | Uninit | Init (value : runtime_value).

Inductive local_storage :=
  | LocalDead
  | LocalUnallocated
  | LocalAllocated (allocation : nat).

Inductive ub_reason :=
  | UbInvalidDeref
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
  | UbInvalidLayout
  | UbPointerArithmeticOverflow
  | UbCopyNonOverlappingOverlap
  | UbReachedUnreachable
  | UbDivisionByZero
  | UbDivisionOverflow.

Definition invalid_deref_reason : ub_reason := UbInvalidDeref.
Definition uninitialized_read_reason : ub_reason := UbReadUninitialized.
Definition dead_read_reason : ub_reason := UbReadDead.
Definition overlapping_copy_reason : ub_reason :=
  UbCopyNonOverlappingOverlap.

Fixpoint set_nth {A : Type} (index : nat) (value : A) (values : list A)
    : option (list A) :=
  match index, values with
  | O, _ :: tail => Some (value :: tail)
  | S index, head :: tail =>
      match set_nth index value tail with
      | Some tail' => Some (head :: tail')
      | None => None
      end
  | _, [] => None
  end.

Record operation_layout := OperationLayout {
  operation_layout_size : nat;
  operation_layout_align : nat;
}.

Definition operation_layout_eqb
    (left right : operation_layout) : bool :=
  Nat.eqb (operation_layout_size left) (operation_layout_size right) &&
  Nat.eqb (operation_layout_align left) (operation_layout_align right).

Inductive operation_type :=
  | TypedOp (shape : value_shape)
  | UntypedOp (layout : operation_layout).

Record memory_value := MemoryValueData {
  memory_value_bytes : list byte;
  memory_value_init : list bool;
  memory_value_provenance : list (option pointer_provenance);
}.

Definition MemoryValue (bytes : list byte) (init : list bool) : memory_value :=
  MemoryValueData bytes init (repeat None (List.length bytes)).

Definition MemoryValueWithProvenance
    (bytes : list byte)
    (init : list bool)
    (provenance : list (option pointer_provenance)) : memory_value :=
  MemoryValueData bytes init provenance.

Inductive operation_value :=
  | OVTyped (value : runtime_value)
  | OVUntyped (layout : operation_layout) (value : memory_value).

Definition int_width_bytes (width : int_width) : nat :=
  match width with
  | W8 => 1
  | W16 => 2
  | W32 => 4
  | W64 | WSize => 8
  | W128 => 16
  end.

Definition int_width_align (width : int_width) : nat :=
  int_width_bytes width.

Definition pointer_bytes : nat := int_width_bytes WSize.

Definition pointer_align : nat := int_width_align WSize.

Fixpoint layouts_for_type (layouts : layout_env) (t : ty)
    : list type_layout :=
  match layouts with
  | [] => []
  | layout :: layouts =>
      if ty_eqb (layout_ty layout) t then
        layout :: layouts_for_type layouts t
      else layouts_for_type layouts t
  end.

Definition find_type_layout (layouts : layout_env) (t : ty)
    : option type_layout :=
  match layouts_for_type layouts t with
  | [layout] => Some layout
  | _ => None
  end.

Fixpoint shape_of_layout_ty_fuel (fuel : nat) (t : ty)
    : option value_shape :=
  match fuel with
  | O => None
  | S fuel =>
      let fix shapes_of_tys (tys : list ty)
          : option (list value_shape) :=
        match tys with
        | [] => Some []
        | t :: tys =>
            match shape_of_layout_ty_fuel fuel t, shapes_of_tys tys with
            | Some shape, Some shapes => Some (shape :: shapes)
            | _, _ => None
            end
        end in
      match t with
      | TNever => Some ShapeNever
      | TBool => Some ShapeBool
      | TChar => Some ShapeChar
      | TFloat w => Some (ShapeFloat (float_width_bits w))
      | TInt width | TUint width => Some (ShapeBits width)
      | TRef _ pointee kind =>
          match shape_of_layout_ty_fuel fuel pointee with
          | Some shape => Some (ShapeReference kind shape)
          | None => None
          end
      | TRawPtr pointee kind =>
          match shape_of_layout_ty_fuel fuel pointee with
          | Some shape => Some (ShapeRawPointer kind shape)
          | None => None
          end
      | TArray element length =>
          match shape_of_layout_ty_fuel fuel element, const_nat length with
          | Some shape, Some n => Some (ShapeArray shape n)
          | _, _ => None
          end
      | TSlice element =>
          match shape_of_layout_ty_fuel fuel element with
          | Some shape => Some (ShapeSlice shape)
          | None => None
          end
      | TStr => Some ShapeStr
      | TTuple fields =>
          match fields with
          | [] => Some ShapeUnit
          | _ =>
              match shapes_of_tys fields with
              | Some shapes => Some (ShapeTuple shapes)
              | None => None
              end
          end
      | TAdt _ _ => Some (ShapeAdtType t)
      | TFnDef _ _ => Some ShapeUnit
      | TClosure _ args =>
          match closure_upvars args with
          | Some u => shape_of_layout_ty_fuel fuel u
          | None => None
          end
      | TPat base _ => shape_of_layout_ty_fuel fuel base
      | TFnPtr _ => Some (ShapeRawPointer Imm ShapeUnit)
      | _ => None
      end
  end.

Definition shape_of_layout_ty (t : ty) : option value_shape :=
  shape_of_layout_ty_fuel 64%nat t.

Fixpoint shape_matches_ty_fuel (fuel : nat) (shape : value_shape)
    (t : ty) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      let fix shapes_match_tys (shapes : list value_shape)
          (tys : list ty) : bool :=
        match shapes, tys with
        | [], [] => true
        | shape :: shapes, t :: tys =>
            shape_matches_ty_fuel fuel shape t && shapes_match_tys shapes tys
        | _, _ => false
        end in
      match shape, t with
      | ShapeUnit, TTuple [] => true
      | ShapeUnit, TFnDef _ _ => true
      | ShapeNever, TNever => true
      | ShapeBool, TBool => true
      | ShapeChar, TChar => true
      | ShapeFloat bits, TFloat w => Nat.eqb bits (float_width_bits w)
      | ShapeBits width, TInt width' | ShapeBits width, TUint width' =>
          int_width_eqb width width'
      | ShapePointer pointee, TRef _ pointee_ty _
      | ShapePointer pointee, TRawPtr pointee_ty _ =>
          shape_matches_ty_fuel fuel pointee pointee_ty
      | ShapeReference kind pointee, TRef _ pointee_ty kind'
      | ShapeRawPointer kind pointee, TRawPtr pointee_ty kind' =>
          match kind, kind' with
          | Imm, Imm | Mut, Mut =>
              shape_matches_ty_fuel fuel pointee pointee_ty
          | _, _ => false
          end
      | ShapeTuple fields, TTuple field_tys =>
          shapes_match_tys fields field_tys
      | ShapeTuple fields, TArray element length =>
          match const_nat length with
          | Some n =>
              Nat.eqb (List.length fields) n &&
              forallb (fun shape => shape_matches_ty_fuel fuel shape element) fields
          | None => false
          end
      | ShapeArray element length, TArray element' length' =>
          match const_nat length' with
          | Some n =>
              Nat.eqb length n && shape_matches_ty_fuel fuel element element'
          | None => false
          end
      | ShapeSlice element, TSlice element' =>
          shape_matches_ty_fuel fuel element element'
      | ShapeStr, TStr => true
      | ShapeAdtType exact, TAdt _ _ => ty_eqb exact t
      | ShapeAdt declaration _ _, TAdt declaration' _ =>
          String.eqb declaration declaration'
      | _, TClosure _ args =>
          match closure_upvars args with
          | Some u => shape_matches_ty_fuel fuel shape u
          | None => false
          end
      | _, TPat base _ => shape_matches_ty_fuel fuel shape base
      | ShapeRawPointer _ ShapeUnit, TFnPtr _ | ShapePointer ShapeUnit, TFnPtr _ => true
      | _, _ => false
      end
  end.

Definition shape_matches_ty (shape : value_shape) (t : ty) : bool :=
  shape_matches_ty_fuel 64 shape t.

Fixpoint layouts_for_shape (layouts : layout_env) (shape : value_shape)
    : list type_layout :=
  match layouts with
  | [] => []
  | layout :: layouts =>
      if shape_matches_ty shape (layout_ty layout) then
        layout :: layouts_for_shape layouts shape
      else layouts_for_shape layouts shape
  end.

Definition find_layout_for_shape (layouts : layout_env) (shape : value_shape)
    : option type_layout :=
  match layouts_for_shape layouts shape with
  | [layout] => Some layout
  | _ => None
  end.

Fixpoint shape_layout_supported_fuel
    (fuel : nat) (layouts : layout_env) (shape : value_shape) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      let fix shapes_supported (shapes : list value_shape) : bool :=
        match shapes with
        | [] => true
        | shape :: shapes =>
            shape_layout_supported_fuel fuel layouts shape &&
            shapes_supported shapes
        end in
      match shape with
      | ShapeUnit | ShapeNever | ShapeBool | ShapeChar | ShapeFloat _ | ShapeBits _
      | ShapeStr => true
      | ShapePointer pointee | ShapeSlice pointee =>
          shape_layout_supported_fuel fuel layouts pointee
      | ShapeReference _ pointee | ShapeRawPointer _ pointee =>
          match find_layout_for_shape layouts shape with
          | Some _ => shape_layout_supported_fuel fuel layouts pointee
          | None => false
          end
      | ShapeArray element _ =>
          match find_layout_for_shape layouts shape with
          | Some _ => shape_layout_supported_fuel fuel layouts element
          | None => false
          end
      | ShapeTuple fields | ShapeAdt _ _ fields =>
          match find_layout_for_shape layouts shape with
          | Some _ => shapes_supported fields
          | None => false
          end
      | ShapeAdtType adt =>
          match find_type_layout layouts adt with
          | Some layout =>
              let fix tys_supported (tys : list ty) : bool :=
                match tys with
                | [] => true
                | t :: tys =>
                    match shape_of_layout_ty_fuel fuel t with
                    | Some shape =>
                        shape_layout_supported_fuel fuel layouts shape &&
                        tys_supported tys
                    | None => false
                    end
                end in
              let top_supported :=
                tys_supported (layout_field_types layout) in
              let variants_supported :=
                match layout_variants layout with
                | VariantsEmpty | VariantsSingle _ => true
                | VariantsMultiple _ _ _ variants =>
                    forallb (fun variant =>
                      tys_supported (variant_field_types variant)) variants
                end in
              top_supported && variants_supported
          | None => false
          end
      end
  end.

Definition shape_layout_supported
    (layouts : layout_env) (shape : value_shape) : bool :=
  shape_layout_supported_fuel 64%nat layouts shape.

Definition scalar_layout_size (scalar : scalar_layout) : nat :=
  match scalar_primitive scalar with
  | PrimInt bits _ | PrimFloat bits | PrimPointer _ bits =>
      Nat.div bits 8
  end.

Definition layout_field_offset (layout : type_layout) (index : nat)
    : option nat :=
  match layout_fields layout with
  | FieldsPrimitive => None
  | FieldsUnion count =>
      if Nat.ltb index count then Some 0%nat else None
  | FieldsArray stride count =>
      if Nat.ltb index count then Some (index * stride)%nat else None
  | FieldsArbitrary offsets => nth_error offsets index
  end.

Definition layout_field_offsets (layout : type_layout) : list nat :=
  match layout_fields layout with
  | FieldsPrimitive => []
  | FieldsUnion count => repeat 0%nat count
  | FieldsArray stride count =>
      map (fun index => (index * stride)%nat) (seq 0 count)
  | FieldsArbitrary offsets => offsets
  end.

Definition layout_variant (layout : type_layout) (variant : nat)
    : option variant_layout :=
  match layout_variants layout with
  | VariantsEmpty => None
  | VariantsSingle index =>
      if Nat.eqb index variant then
        Some (VariantLayoutWithFields index (layout_size layout)
          (layout_uninhabited layout) (layout_field_types layout)
          (layout_field_offsets layout) (layout_abi layout))
      else None
  | VariantsMultiple _ _ _ variants =>
      find (fun layout => Nat.eqb (variant_index layout) variant) variants
  end.

Definition layout_variant_field_types (layout : type_layout) (variant : nat)
    : option (list ty) :=
  match layout_variant layout variant with
  | Some variant_layout => Some (variant_field_types variant_layout)
  | None => None
  end.

Fixpoint shapes_of_layout_tys (tys : list ty)
    : option (list value_shape) :=
  match tys with
  | [] => Some []
  | t :: tys =>
      match shape_of_layout_ty t, shapes_of_layout_tys tys with
      | Some shape, Some shapes => Some (shape :: shapes)
      | _, _ => None
      end
  end.

Definition layout_variant_field_shapes
    (layout : type_layout) (variant : nat)
    : option (list value_shape) :=
  match layout_variant_field_types layout variant with
  | Some tys => shapes_of_layout_tys tys
  | None => None
  end.

Definition layout_variant_field_offset (layout : type_layout)
    (variant field : nat) : option nat :=
  match layout_variant layout variant with
  | Some variant_layout =>
      nth_error (variant_field_offsets variant_layout) field
  | None => None
  end.

Definition shape_recursion_fuel : nat := 64%nat.

Definition shape_is_unsized (shape : value_shape) : bool :=
  match shape with
  | ShapeSlice _ | ShapeStr => true
  | _ => false
  end.

Definition pointer_shape_size (pointee : value_shape) : nat :=
  if shape_is_unsized pointee then (2 * pointer_bytes)%nat
  else pointer_bytes.

Definition pointer_metadata_matches_shape
    (pointee : value_shape) (metadata : pointer_metadata) : bool :=
  match pointee, metadata with
  | ShapeSlice _, PointerLength _ | ShapeStr, PointerLength _ => true
  | ShapeSlice _, _ | ShapeStr, _ => false
  | _, PointerThin => true
  | _, _ => false
  end.

Fixpoint shape_size_fuel (fuel : nat) (shape : value_shape) : nat :=
  match fuel with
  | O => 0%nat
  | S fuel =>
      let fix shapes_size (shapes : list value_shape) : nat :=
        match shapes with
        | [] => 0%nat
        | shape :: shapes => (shape_size_fuel fuel shape + shapes_size shapes)%nat
        end in
      match shape with
      | ShapeUnit | ShapeNever => 0%nat
      | ShapeBool => 1%nat
      | ShapeChar => 4%nat
      | ShapeFloat bits => Nat.div bits 8
      | ShapeBits width => int_width_bytes width
      | ShapePointer pointee | ShapeReference _ pointee
      | ShapeRawPointer _ pointee => pointer_shape_size pointee
      | ShapeArray element length =>
          (length * shape_size_fuel fuel element)%nat
      | ShapeSlice _ | ShapeStr => 0%nat
      | ShapeTuple fields => shapes_size fields
      | ShapeAdtType _ => 0%nat
      | ShapeAdt _ _ fields => (pointer_bytes + shapes_size fields)%nat
      end
  end.

Definition shape_size (shape : value_shape) : nat :=
  shape_size_fuel shape_recursion_fuel shape.

Definition shape_size_with_layouts (layouts : layout_env)
    (shape : value_shape) : nat :=
  match find_layout_for_shape layouts shape with
  | Some layout => layout_size layout
  | None => shape_size shape
  end.

Fixpoint shape_align_fuel (fuel : nat) (shape : value_shape) : nat :=
  match fuel with
  | O => 1%nat
  | S fuel =>
      let fix shapes_align (shapes : list value_shape) : nat :=
        match shapes with
        | [] => 1%nat
        | shape :: shapes =>
            Nat.max (shape_align_fuel fuel shape) (shapes_align shapes)
        end in
      match shape with
      | ShapeUnit | ShapeNever => 1%nat
      | ShapeBool => 1%nat
      | ShapeChar => 4%nat
      | ShapeFloat bits => Nat.max 1 (Nat.div bits 8)
      | ShapeBits width => int_width_align width
      | ShapePointer _ | ShapeReference _ _ | ShapeRawPointer _ _ =>
          pointer_align
      | ShapeArray element _ | ShapeSlice element =>
          shape_align_fuel fuel element
      | ShapeStr => 1%nat
      | ShapeTuple fields => shapes_align fields
      | ShapeAdtType _ => 1%nat
      | ShapeAdt _ _ fields => Nat.max pointer_align (shapes_align fields)
      end
  end.

Definition shape_align (shape : value_shape) : nat :=
  shape_align_fuel shape_recursion_fuel shape.

Definition shape_align_with_layouts (layouts : layout_env)
    (shape : value_shape) : nat :=
  match find_layout_for_shape layouts shape with
  | Some layout => layout_align layout
  | None => shape_align shape
  end.

Definition layout_of_shape_with_layouts (layouts : layout_env)
    (shape : value_shape) : operation_layout :=
  OperationLayout
    (shape_size_with_layouts layouts shape)
    (shape_align_with_layouts layouts shape).

Definition operation_type_layout (operation : operation_type)
    : operation_layout :=
  match operation with
  | TypedOp shape => layout_of_shape_with_layouts [] shape
  | UntypedOp layout => layout
  end.

Definition operation_type_layout_with_layouts
    (layouts : layout_env) (operation : operation_type) : operation_layout :=
  match operation with
  | TypedOp shape => layout_of_shape_with_layouts layouts shape
  | UntypedOp layout => layout
  end.

Definition repeat_operation_layout (layout : operation_layout) (count : nat)
    : operation_layout :=
  OperationLayout
    (count * operation_layout_size layout)
    (operation_layout_align layout).

Fixpoint shape_of_value_fuel (fuel : nat) (value : runtime_value)
    : value_shape :=
  match fuel with
  | O => ShapeUnit
  | S fuel =>
      let fix shapes_of_values (values : list runtime_value)
          : list value_shape :=
        match values with
        | [] => []
        | value :: values =>
            shape_of_value_fuel fuel value :: shapes_of_values values
        end in
      match value with
      | VUnit => ShapeUnit
      | VBool _ => ShapeBool
      | VChar _ => ShapeChar
      | VFloatBits bits _ => ShapeFloat bits
      | VBits width _ => ShapeBits width
      | VPointerValue pointee _ => ShapePointer pointee
      | VFunction _ => ShapeUnit
      | VArray element fields => ShapeArray element (List.length fields)
      | VTuple fields => ShapeTuple (shapes_of_values fields)
      | VAdt declaration variant fields =>
          ShapeAdt declaration variant (shapes_of_values fields)
      | VUnion declaration _ _ => ShapeAdt declaration 0%nat []
      | VRawAggregate shape _ _ _ => shape
      end
  end.

Definition shape_of_value (value : runtime_value) : value_shape :=
  shape_of_value_fuel shape_recursion_fuel value.

Definition valid_byte (value : byte) : bool :=
  (0 <=? value) && (value <? 256).

Fixpoint valid_bytes (bytes : list byte) : bool :=
  match bytes with
  | [] => true
  | byte :: bytes => valid_byte byte && valid_bytes bytes
  end.

Fixpoint all_initialized (init : list bool) : bool :=
  match init with
  | [] => true
  | initialized :: init => initialized && all_initialized init
  end.

Definition range_available {A : Type} (offset length : nat) (values : list A)
    : bool :=
  Nat.leb (offset + length) (List.length values).

Definition initialized_range (offset length : nat) (init : list bool) : bool :=
  range_available offset length init &&
  all_initialized (firstn length (skipn offset init)).

Definition aligned_offset (offset alignment : nat) : bool :=
  match alignment with
  | O => false
  | S _ => Nat.eqb (Nat.modulo offset alignment) 0
  end.

Fixpoint raw_provenance_init_consistent
    (init : list bool) (provenance : list (option pointer_provenance)) : bool :=
  match init, provenance with
  | [], [] => true
  | initialized :: init, tag :: provenance =>
      (initialized ||
        match tag with None => true | Some _ => false end) &&
      raw_provenance_init_consistent init provenance
  | _, _ => false
  end.

Fixpoint valid_runtime_value_fuel (fuel : nat) (value : runtime_value)
    : bool :=
  match fuel with
  | O => false
  | S fuel =>
      let fix valid_runtime_values (values : list runtime_value) : bool :=
        match values with
        | [] => true
        | value :: values =>
            valid_runtime_value_fuel fuel value && valid_runtime_values values
        end in
      match value with
      | VUnit => true
      | VBool _ => true
      | VChar value =>
          (0 <=? value) && (value <=? 1114111) &&
          negb ((55296 <=? value) && (value <=? 57343))
      | VFloatBits width bits =>
          ((Nat.eqb width 16 || Nat.eqb width 32 || Nat.eqb width 64 ||
            Nat.eqb width 128) &&
           (0 <=? bits) && (bits <? 2 ^ Z.of_nat width))
      | VBits width bits =>
          (0 <=? bits) &&
          (bits <? 2 ^ Z.of_nat (8 * int_width_bytes width)%nat)
      | VPointerValue _ pointer =>
          let address_ok :=
            (0 <=? pointer_address pointer) &&
            (pointer_address pointer <? 2 ^ Z.of_nat (8 * pointer_bytes)%nat) in
          let metadata_ok :=
            match pointer_metadata_of pointer with
            | PointerThin => true
            | PointerLength length =>
                Z.of_nat length <? 2 ^ Z.of_nat (8 * pointer_bytes)%nat
            | PointerVTable _ address =>
                (0 <=? address) &&
                (address <? 2 ^ Z.of_nat (8 * pointer_bytes)%nat)
            end in
          address_ok && metadata_ok
      | VFunction _ => false
      | VArray _ fields => valid_runtime_values fields
      | VTuple fields => valid_runtime_values fields
      | VAdt _ _ fields => valid_runtime_values fields
      | VUnion _ _ field => valid_runtime_value_fuel fuel field
      | VRawAggregate shape bytes init provenance =>
          negb (shape_is_unsized shape) && valid_bytes bytes &&
          Nat.eqb (List.length bytes) (List.length init) &&
          Nat.eqb (List.length bytes) (List.length provenance) &&
          raw_provenance_init_consistent init provenance
      end
  end.

Definition valid_runtime_value (value : runtime_value) : bool :=
  valid_runtime_value_fuel shape_recursion_fuel value.

Fixpoint encode_unsigned (length : nat) (bits : Z) : list byte :=
  match length with
  | O => []
  | S length => Z.modulo bits 256 :: encode_unsigned length (Z.div bits 256)
  end.

Fixpoint decode_unsigned (bytes : list byte) : Z :=
  match bytes with
  | [] => 0
  | byte :: bytes => byte + 256 * decode_unsigned bytes
  end.

Fixpoint encode_value_fuel (fuel : nat) (value : runtime_value)
    : option (list byte) :=
  match fuel with
  | O => None
  | S fuel =>
      let fix encode_values (values : list runtime_value)
          : option (list byte) :=
        match values with
        | [] => Some []
        | value :: values =>
            match encode_value_fuel fuel value, encode_values values with
            | Some bytes, Some bytes' => Some (bytes ++ bytes')%list
            | _, _ => None
            end
        end in
      if valid_runtime_value value then
        match value with
        | VUnit => Some []
        | VBool false => Some [0]
        | VBool true => Some [1]
        | VChar value => Some (encode_unsigned 4 value)
        | VFloatBits width bits =>
            Some (encode_unsigned (Nat.div width 8) bits)
        | VBits width bits => Some (encode_unsigned (int_width_bytes width) bits)
        | VPointerValue _ pointer =>
            match pointer_metadata_of pointer with
            | PointerThin =>
                Some (encode_unsigned pointer_bytes
                  (pointer_address pointer))
            | PointerLength length =>
                Some (encode_unsigned pointer_bytes
                    (pointer_address pointer) ++
                  encode_unsigned pointer_bytes (Z.of_nat length))%list
            | PointerVTable _ address =>
                Some (encode_unsigned pointer_bytes
                    (pointer_address pointer) ++
                  encode_unsigned pointer_bytes address)%list
            end
        | VFunction _ => None
        | VArray _ fields => encode_values fields
        | VTuple fields => encode_values fields
        | VAdt _ variant fields =>
            match encode_values fields with
            | Some bytes =>
                Some (encode_unsigned pointer_bytes (Z.of_nat variant) ++ bytes)%list
            | None => None
            end
        | VUnion _ _ _ => None
        | VRawAggregate _ bytes _ _ => Some bytes
        end
      else None
  end.

Definition encode_value (value : runtime_value) : option (list byte) :=
  encode_value_fuel shape_recursion_fuel value.

Fixpoint value_shape_eqb_fuel (fuel : nat)
    (lhs rhs : value_shape) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      let fix value_shapes_eqb (lefts rights : list value_shape) : bool :=
        match lefts, rights with
        | [], [] => true
        | lhs :: lefts, rhs :: rights =>
            value_shape_eqb_fuel fuel lhs rhs &&
            value_shapes_eqb lefts rights
        | _, _ => false
        end in
      match lhs, rhs with
      | ShapeUnit, ShapeUnit => true
      | ShapeNever, ShapeNever => true
      | ShapeBool, ShapeBool => true
      | ShapeChar, ShapeChar => true
      | ShapeFloat left_bits, ShapeFloat right_bits =>
          Nat.eqb left_bits right_bits
      | ShapeBits left_width, ShapeBits right_width =>
          int_width_eqb left_width right_width
      | ShapePointer left_pointee, ShapePointer right_pointee =>
          value_shape_eqb_fuel fuel left_pointee right_pointee
      | ShapeReference left_kind left_pointee,
          ShapeReference right_kind right_pointee
      | ShapeRawPointer left_kind left_pointee,
          ShapeRawPointer right_kind right_pointee =>
          match left_kind, right_kind with
          | Imm, Imm | Mut, Mut =>
              value_shape_eqb_fuel fuel left_pointee right_pointee
          | _, _ => false
          end
      | ShapeArray left_element left_length,
          ShapeArray right_element right_length =>
          Nat.eqb left_length right_length &&
          value_shape_eqb_fuel fuel left_element right_element
      | ShapeSlice left_element, ShapeSlice right_element =>
          value_shape_eqb_fuel fuel left_element right_element
      | ShapeStr, ShapeStr => true
      | ShapeTuple left_fields, ShapeTuple right_fields =>
          value_shapes_eqb left_fields right_fields
      | ShapeAdtType left_ty, ShapeAdtType right_ty =>
          ty_eqb left_ty right_ty
      | ShapeAdt left_decl left_variant left_fields,
          ShapeAdt right_decl right_variant right_fields =>
          String.eqb left_decl right_decl &&
          Nat.eqb left_variant right_variant &&
          value_shapes_eqb left_fields right_fields
      | _, _ => false
      end
  end.

Definition value_shape_eqb (lhs rhs : value_shape) : bool :=
  value_shape_eqb_fuel shape_recursion_fuel lhs rhs.

Fixpoint encode_value_as_fuel (fuel : nat) (shape : value_shape)
    (value : runtime_value) : option (list byte) :=
  match fuel with
  | O => None
  | S fuel =>
      let fix encode_values_as (shapes : list value_shape)
          (values : list runtime_value) : option (list byte) :=
        match shapes, values with
        | [], [] => Some []
        | shape :: shapes, value :: values =>
            match encode_value_as_fuel fuel shape value,
                encode_values_as shapes values with
            | Some bytes, Some bytes' => Some (bytes ++ bytes')%list
            | _, _ => None
            end
        | _, _ => None
        end in
      if valid_runtime_value value then
        match shape, value with
        | ShapeUnit, VUnit => Some []
        | ShapeNever, _ => None
        | ShapeBool, VBool false => Some [0]
        | ShapeBool, VBool true => Some [1]
        | ShapeChar, VChar value => Some (encode_unsigned 4 value)
        | ShapeFloat bits, VFloatBits bits' value =>
            if Nat.eqb bits bits' then
              Some (encode_unsigned (Nat.div bits 8) value)
            else None
        | ShapeBits width, VBits width' bits =>
            if int_width_eqb width width' then
              Some (encode_unsigned (int_width_bytes width) bits)
            else None
        | ShapePointer pointee, VPointerValue pointee' pointer
        | ShapeReference _ pointee, VPointerValue pointee' pointer
        | ShapeRawPointer _ pointee, VPointerValue pointee' pointer =>
            if value_shape_eqb pointee pointee' &&
                pointer_metadata_matches_shape pointee
                  (pointer_metadata_of pointer) then
              match pointer_metadata_of pointer with
              | PointerThin =>
                  Some (encode_unsigned pointer_bytes
                    (pointer_address pointer))
              | PointerLength length =>
                  Some (encode_unsigned pointer_bytes
                      (pointer_address pointer) ++
                    encode_unsigned pointer_bytes (Z.of_nat length))%list
              | PointerVTable _ address =>
                  Some (encode_unsigned pointer_bytes
                      (pointer_address pointer) ++
                    encode_unsigned pointer_bytes address)%list
              end
            else None
        | ShapeArray element length, VArray element' values =>
            if value_shape_eqb element element' &&
                Nat.eqb (List.length values) length then
              encode_values_as (repeat element length) values
            else None
        | ShapeArray element length, VTuple values =>
            if Nat.eqb (List.length values) length then
              encode_values_as (repeat element length) values
            else None
        | ShapeTuple shapes, VTuple values => encode_values_as shapes values
        | ShapeAdtType _, _ => None
        | ShapeAdt declaration variant shapes,
            VAdt declaration' variant' values =>
            if String.eqb declaration declaration' && Nat.eqb variant variant' then
              match encode_values_as shapes values with
              | Some bytes =>
                  Some (encode_unsigned pointer_bytes (Z.of_nat variant) ++
                    bytes)%list
              | None => None
              end
            else None
        | _, VUnion _ _ _ => None
        | expected, VRawAggregate actual bytes _ _ =>
            if value_shape_eqb expected actual then Some bytes else None
        | _, _ => None
        end
      else None
  end.

Definition encode_value_as (shape : value_shape) (value : runtime_value)
    : option (list byte) :=
  encode_value_as_fuel shape_recursion_fuel shape value.

Fixpoint nat_list_eqb (lefts rights : list nat) : bool :=
  match lefts, rights with
  | [], [] => true
  | left_id :: lefts', right_id :: rights' =>
      Nat.eqb left_id right_id && nat_list_eqb lefts' rights'
  | _, _ => false
  end.

Definition pointer_provenance_eqb
    (left right : pointer_provenance) : bool :=
  match left, right with
  | ProvenanceNone, ProvenanceNone => true
  | ProvenanceAllocation left_id, ProvenanceAllocation right_id =>
      Nat.eqb left_id right_id
  | ProvenanceExposed left_ids, ProvenanceExposed right_ids =>
      nat_list_eqb left_ids right_ids
  | ProvenanceFunction left_name, ProvenanceFunction right_name =>
      String.eqb left_name right_name
  | _, _ => false
  end.

Fixpoint all_provenance_is
    (expected : option pointer_provenance)
    (values : list (option pointer_provenance)) : bool :=
  match values with
  | [] => true
  | value :: values =>
      let equal :=
        match expected, value with
        | None, None => true
        | Some expected, Some value =>
            pointer_provenance_eqb expected value
        | _, _ => false
        end in
      equal && all_provenance_is expected values
  end.

Fixpoint encode_value_provenance_as_fuel
    (fuel : nat) (shape : value_shape) (value : runtime_value)
    : option (list (option pointer_provenance)) :=
  match fuel with
  | O => None
  | S fuel =>
      let fix encode_values (shapes : list value_shape)
          (values : list runtime_value)
          : option (list (option pointer_provenance)) :=
        match shapes, values with
        | [], [] => Some []
        | shape :: shapes, value :: values =>
            match encode_value_provenance_as_fuel fuel shape value,
                encode_values shapes values with
            | Some first, Some rest => Some (first ++ rest)%list
            | _, _ => None
            end
        | _, _ => None
        end in
      match shape, value with
      | ShapeUnit, VUnit => Some []
      | ShapeNever, _ => None
      | ShapeBool, VBool _ => Some [None]
      | ShapeChar, VChar _ => Some (repeat None 4)
      | ShapeFloat bits, VFloatBits bits' _ =>
          if Nat.eqb bits bits' then Some (repeat None (Nat.div bits 8))
          else None
      | ShapeBits width, VBits width' _ =>
          if int_width_eqb width width' then
            Some (repeat None (int_width_bytes width))
          else None
      | ShapePointer pointee, VPointerValue pointee' pointer
      | ShapeReference _ pointee, VPointerValue pointee' pointer
      | ShapeRawPointer _ pointee, VPointerValue pointee' pointer =>
          if value_shape_eqb pointee pointee' then
            let tag :=
              match pointer_provenance_of pointer with
              | ProvenanceNone => None
              | provenance => Some provenance
              end in
            Some (repeat tag pointer_bytes ++
              repeat None (pointer_shape_size pointee - pointer_bytes))%list
          else None
      | ShapeArray element length, VArray element' values =>
          if value_shape_eqb element element' &&
              Nat.eqb (List.length values) length then
            encode_values (repeat element length) values
          else None
      | ShapeArray element length, VTuple values =>
          if Nat.eqb (List.length values) length then
            encode_values (repeat element length) values
          else None
      | ShapeTuple shapes, VTuple values => encode_values shapes values
      | ShapeAdtType _, _ => None
      | ShapeAdt declaration variant shapes,
          VAdt declaration' variant' values =>
          if String.eqb declaration declaration' && Nat.eqb variant variant'
          then
            match encode_values shapes values with
            | Some fields => Some (repeat None pointer_bytes ++ fields)%list
            | None => None
            end
          else None
      | _, VUnion _ _ _ => None
      | expected, VRawAggregate actual _ _ provenance =>
          if value_shape_eqb expected actual then Some provenance else None
      | _, _ => None
      end
  end.

Definition encode_value_provenance_as
    (shape : value_shape) (value : runtime_value)
    : option (list (option pointer_provenance)) :=
  encode_value_provenance_as_fuel shape_recursion_fuel shape value.

Definition encode_typed_memory_value
    (shape : value_shape) (value : runtime_value) : option memory_value :=
  match value with
  | VRawAggregate actual bytes init provenance =>
      if value_shape_eqb shape actual &&
          Nat.eqb (List.length bytes) (shape_size shape) &&
          Nat.eqb (List.length init) (shape_size shape) &&
          Nat.eqb (List.length provenance) (shape_size shape) then
        Some (MemoryValueWithProvenance bytes init provenance)
      else None
  | _ =>
      match encode_value_as shape value,
          encode_value_provenance_as shape value with
      | Some bytes, Some provenance =>
          if Nat.eqb (List.length bytes) (shape_size shape) &&
              Nat.eqb (List.length provenance) (shape_size shape) then
            Some (MemoryValueWithProvenance bytes
              (repeat true (shape_size shape)) provenance)
          else None
      | _, _ => None
      end
  end.

Fixpoint decode_value_fuel (fuel : nat) (shape : value_shape)
    (bytes : list byte) : option runtime_value :=
  match fuel with
  | O => None
  | S fuel =>
      let fix decode_values (shapes : list value_shape) (bytes : list byte)
          : option (list runtime_value) :=
        match shapes with
        | [] => Some []
        | shape :: shapes =>
            let size := shape_size shape in
            match decode_value_fuel fuel shape (firstn size bytes),
                decode_values shapes (skipn size bytes) with
            | Some value, Some values => Some (value :: values)
            | _, _ => None
            end
        end in
      if Nat.eqb (List.length bytes) (shape_size shape) && valid_bytes bytes then
        match shape with
        | ShapeUnit => Some VUnit
        | ShapeNever => None
        | ShapeBool =>
            match bytes with
            | [0] => Some (VBool false)
            | [1] => Some (VBool true)
            | _ => None
            end
        | ShapeChar =>
            let value := decode_unsigned bytes in
            if (0 <=? value) && (value <=? 1114111) &&
                negb ((55296 <=? value) && (value <=? 57343)) then
              Some (VChar value)
            else None
        | ShapeFloat bits =>
            if Nat.eqb (List.length bytes) (Nat.div bits 8) then
              Some (VFloatBits bits (decode_unsigned bytes))
            else None
        | ShapeBits width => Some (VBits width (decode_unsigned bytes))
        | ShapePointer pointee | ShapeReference _ pointee
        | ShapeRawPointer _ pointee =>
            let address := decode_unsigned (firstn pointer_bytes bytes) in
            if shape_is_unsized pointee then
              let metadata :=
                decode_unsigned (firstn pointer_bytes
                  (skipn pointer_bytes bytes)) in
              Some (VPointerValue pointee
                (PointerValue ProvenanceNone address
                  (PointerLength (Z.to_nat metadata))))
            else Some (VPointerValue pointee
              (PointerValue ProvenanceNone address PointerThin))
        | ShapeArray element length =>
            match decode_values (repeat element length) bytes with
            | Some values => Some (VArray element values)
            | None => None
            end
        | ShapeSlice _ | ShapeStr => None
        | ShapeTuple fields =>
            match decode_values fields bytes with
            | Some values => Some (VTuple values)
            | None => None
            end
        | ShapeAdtType _ => None
        | ShapeAdt declaration variant fields =>
            let discriminant := firstn pointer_bytes bytes in
            let fields_bytes := skipn pointer_bytes bytes in
            if Z.eqb (decode_unsigned discriminant) (Z.of_nat variant) then
              match decode_values fields fields_bytes with
              | Some values => Some (VAdt declaration variant values)
              | None => None
              end
            else None
        end
      else None
  end.

Definition decode_value (shape : value_shape) (bytes : list byte)
    : option runtime_value :=
  decode_value_fuel shape_recursion_fuel shape bytes.

Fixpoint decode_value_with_provenance_fuel
    (fuel : nat) (shape : value_shape) (bytes : list byte)
    (provenance : list (option pointer_provenance))
    : option runtime_value :=
  match fuel with
  | O => None
  | S fuel =>
      let fix decode_values (shapes : list value_shape)
          (bytes : list byte)
          (provenance : list (option pointer_provenance))
          : option (list runtime_value) :=
        match shapes with
        | [] =>
            if Nat.eqb (List.length bytes) 0 &&
                Nat.eqb (List.length provenance) 0 then Some []
            else None
        | shape :: shapes =>
            let size := shape_size shape in
            match decode_value_with_provenance_fuel fuel shape
                    (firstn size bytes) (firstn size provenance),
                decode_values shapes (skipn size bytes)
                  (skipn size provenance) with
            | Some value, Some values => Some (value :: values)
            | _, _ => None
            end
        end in
      if Nat.eqb (List.length bytes) (shape_size shape) &&
          Nat.eqb (List.length provenance) (shape_size shape) &&
          valid_bytes bytes then
        match shape with
        | ShapePointer pointee | ShapeReference _ pointee
        | ShapeRawPointer _ pointee =>
            let address_bytes := firstn pointer_bytes bytes in
            let tags := firstn pointer_bytes provenance in
            let metadata_bytes := firstn pointer_bytes
              (skipn pointer_bytes bytes) in
            let metadata_tags := firstn pointer_bytes
              (skipn pointer_bytes provenance) in
            match tags with
            | [] => None
            | first_tag :: _ =>
                if all_provenance_is first_tag tags then
                  let decoded_provenance :=
                    match first_tag with
                    | Some provenance => provenance
                    | None => ProvenanceNone
                    end in
                  let decoded_address := decode_unsigned address_bytes in
                  if shape_is_unsized pointee then
                    if all_provenance_is None metadata_tags then
                      Some (VPointerValue pointee
                        (PointerValue decoded_provenance decoded_address
                          (PointerLength
                            (Z.to_nat (decode_unsigned metadata_bytes)))))
                    else None
                  else Some (VPointerValue pointee
                    (PointerValue decoded_provenance decoded_address
                      PointerThin))
                else None
            end
        | ShapeArray element length =>
            match decode_values (repeat element length) bytes provenance with
            | Some values => Some (VArray element values)
            | None => None
            end
        | ShapeSlice _ | ShapeStr => None
        | ShapeTuple fields =>
            match decode_values fields bytes provenance with
            | Some values => Some (VTuple values)
            | None => None
            end
        | ShapeAdtType _ => None
        | ShapeAdt declaration variant fields =>
            let discriminant := firstn pointer_bytes bytes in
            let fields_bytes := skipn pointer_bytes bytes in
            let fields_provenance := skipn pointer_bytes provenance in
            if Z.eqb (decode_unsigned discriminant) (Z.of_nat variant) then
              match decode_values fields fields_bytes fields_provenance with
              | Some values => Some (VAdt declaration variant values)
              | None => None
              end
            else None
        | _ =>
            if all_provenance_is None provenance then
              decode_value shape bytes
            else None
        end
      else None
  end.

Definition decode_value_with_provenance
    (shape : value_shape) (value : memory_value)
    : option runtime_value :=
  decode_value_with_provenance_fuel shape_recursion_fuel shape
    (memory_value_bytes value) (memory_value_provenance value).

Record memory_policy := MemoryPolicy {
  policy_may_read : nat -> nat -> operation_type -> bool;
  policy_may_write : nat -> nat -> operation_type -> bool;
}.

Definition permissive_memory_policy : memory_policy :=
  MemoryPolicy (fun _ _ _ => true) (fun _ _ _ => true).

Record allocation := AllocationData {
  allocation_size : nat;
  allocation_align : nat;
  allocation_base : Z;
  allocation_shape : value_shape;
  allocation_bytes : list byte;
  allocation_init : list bool;
  allocation_provenance : list (option pointer_provenance);
  allocation_live : bool;
}.

Definition Allocation (size align : nat) (base : Z) (shape : value_shape)
    (bytes : list byte) (init : list bool) (live : bool) : allocation :=
  AllocationData size align base shape bytes init
    (repeat None (List.length bytes)) live.

Definition AllocationWithProvenance (size align : nat) (base : Z) (shape : value_shape)
    (bytes : list byte) (init : list bool)
    (provenance : list (option pointer_provenance)) (live : bool)
    : allocation :=
  AllocationData size align base shape bytes init provenance live.

Definition memory_state := list allocation.

Definition empty_memory : memory_state := [].

Definition allocation_end (a : allocation) : Z :=
  allocation_base a + Z.of_nat (Nat.max 1 (allocation_size a)).

Definition address_space_end : Z := 2 ^ Z.of_nat (8 * pointer_bytes).

Class AddrAlg := {
  choose_base : memory_state -> nat -> nat -> option Z;
  choose_base_positive : forall m size align base,
    choose_base m size align = Some base -> 0 < base;
  choose_base_aligned : forall m size align base,
    choose_base m size align = Some base -> Z.modulo base (Z.of_nat align) = 0;
  choose_base_fits : forall m size align base,
    choose_base m size align = Some base ->
    base + Z.of_nat (Nat.max 1 size) <= address_space_end;
  choose_base_disjoint : forall m size align base a,
    choose_base m size align = Some base -> In a m -> allocation_live a = true ->
    allocation_end a <= base \/ base + Z.of_nat (Nat.max 1 size) <= allocation_base a;
}.

Definition with_base (a : allocation) (base : Z) : allocation :=
  AllocationData (allocation_size a) (allocation_align a) base (allocation_shape a)
    (allocation_bytes a) (allocation_init a) (allocation_provenance a)
    (allocation_live a).

Definition value_allocation (value : runtime_value) : allocation :=
  let shape := shape_of_value value in
  match encode_typed_memory_value shape value with
  | Some raw =>
      AllocationWithProvenance (shape_size shape) (shape_align shape) 0 shape
        (memory_value_bytes raw) (memory_value_init raw)
        (memory_value_provenance raw) true
  | None => Allocation 0 1 0 shape [] [] true
  end.

Definition memory_range_ok
    (policy_check : nat -> nat -> operation_type -> bool)
    (allocation_id offset : nat) (allocation : allocation)
    (operation : operation_type) : bool :=
  let layout := operation_type_layout operation in
  let size := operation_layout_size layout in
  let align := operation_layout_align layout in
  policy_check allocation_id offset operation &&
  allocation_live allocation &&
  Nat.leb (offset + size) (allocation_size allocation) &&
  range_available offset size (allocation_bytes allocation) &&
  range_available offset size (allocation_init allocation) &&
  range_available offset size (allocation_provenance allocation) &&
  Nat.leb align (allocation_align allocation) &&
  aligned_offset offset align.

Inductive access_result (A : Type) :=
  | AccessOk (value : A)
  | AccessUb (reason : ub_reason)
  | AccessFail.

Arguments AccessOk {A} _.
Arguments AccessUb {A} _.
Arguments AccessFail {A}.

Definition access_bind {A B : Type}
    (result : access_result A) (next : A -> access_result B)
    : access_result B :=
  match result with
  | AccessOk value => next value
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition memory_value_size_ok (size : nat) (value : memory_value) : bool :=
  Nat.eqb (List.length (memory_value_bytes value)) size &&
  Nat.eqb (List.length (memory_value_init value)) size &&
  Nat.eqb (List.length (memory_value_provenance value)) size.

Definition blank_memory_value (size : nat) : memory_value :=
  MemoryValueWithProvenance (repeat 0 size) (repeat false size)
    (repeat None size).

Definition slice_memory_value (offset size : nat) (value : memory_value)
    : option memory_value :=
  if range_available offset size (memory_value_bytes value) &&
      range_available offset size (memory_value_init value) &&
      range_available offset size (memory_value_provenance value) then
    Some (MemoryValueWithProvenance
      (firstn size (skipn offset (memory_value_bytes value)))
      (firstn size (skipn offset (memory_value_init value)))
      (firstn size (skipn offset (memory_value_provenance value))))
  else None.

Definition replace_memory_value (offset : nat) (replacement target : memory_value)
    : option memory_value :=
  let size := List.length (memory_value_bytes replacement) in
  if memory_value_size_ok size replacement &&
      memory_value_size_ok (List.length (memory_value_bytes target)) target &&
      range_available offset size (memory_value_bytes target) then
    Some (MemoryValueWithProvenance
      (firstn offset (memory_value_bytes target) ++
        memory_value_bytes replacement ++
        skipn (offset + size) (memory_value_bytes target))
      (firstn offset (memory_value_init target) ++
        memory_value_init replacement ++
        skipn (offset + size) (memory_value_init target))
      (firstn offset (memory_value_provenance target) ++
        memory_value_provenance replacement ++
        skipn (offset + size) (memory_value_provenance target)))%list
  else None.

Fixpoint shape_prefix_size_with_layouts
    (layouts : layout_env) (index : nat) (shapes : list value_shape) : nat :=
  match index, shapes with
  | O, _ => 0%nat
  | S index, shape :: shapes =>
      (shape_size_with_layouts layouts shape +
        shape_prefix_size_with_layouts layouts index shapes)%nat
  | _, [] => 0%nat
  end.

Definition aggregate_field_offset_with_layouts
    (layouts : layout_env) (shape : value_shape)
    (variant index : nat) : option nat :=
  match find_layout_for_shape layouts shape with
  | Some layout =>
      match shape, layout_fields layout with
      | ShapeArray _ length, FieldsArray stride count =>
          if Nat.ltb index length && Nat.ltb index count then
            Some (index * stride)%nat
          else None
      | ShapeAdtType _, _ | ShapeAdt _ _ _, _ =>
          match layout_variant_field_offset layout variant index with
          | Some offset => Some offset
          | None => layout_field_offset layout index
          end
      | _, _ => layout_field_offset layout index
      end
  | None =>
      match shape with
      | ShapeTuple fields =>
          if Nat.ltb index (List.length fields) then
            Some (shape_prefix_size_with_layouts layouts index fields)
          else None
      | ShapeArray element length =>
          if Nat.ltb index length then
            Some (index * shape_size_with_layouts layouts element)%nat
          else None
      | ShapeAdt _ _ fields =>
          if Nat.ltb index (List.length fields) then
            Some (pointer_bytes +
              shape_prefix_size_with_layouts layouts index fields)%nat
          else None
      | _ => None
      end
  end.

Definition scalar_modulus (scalar : scalar_layout) : Z :=
  2 ^ Z.of_nat (8 * scalar_layout_size scalar)%nat.

Definition scalar_in_valid_range (scalar : scalar_layout) (value : Z) : bool :=
  let value := Z.modulo value (scalar_modulus scalar) in
  let start := Z.modulo (scalar_valid_start scalar) (scalar_modulus scalar) in
  let finish := Z.modulo (scalar_valid_end scalar) (scalar_modulus scalar) in
  if start <=? finish then (start <=? value) && (value <=? finish)
  else (start <=? value) || (value <=? finish).

Definition initialized_scalar_value
    (offset : nat) (scalar : scalar_layout) (value : memory_value)
    : access_result Z :=
  if negb (scalar_initialized scalar) then AccessOk 0
  else
    let size := scalar_layout_size scalar in
    match slice_memory_value offset size value with
    | Some raw =>
        if all_initialized (memory_value_init raw) then
          let bits := decode_unsigned (memory_value_bytes raw) in
          match scalar_primitive scalar with
          | PrimPointer _ _ =>
              match memory_value_provenance raw with
              | [] => AccessUb UbInvalidScalar
              | first :: tags =>
                  if all_provenance_is first tags then
                    match first with
                    | Some ProvenanceNone => AccessUb UbInvalidScalar
                    | Some _ => AccessOk bits
                    | None =>
                        if scalar_in_valid_range scalar bits then AccessOk bits
                        else AccessUb UbInvalidScalar
                    end
                  else AccessUb UbInvalidScalar
              end
          | PrimInt _ _ | PrimFloat _ =>
              if all_provenance_is None
                  (memory_value_provenance raw) then
                if scalar_in_valid_range scalar bits then AccessOk bits
                else AccessUb UbInvalidScalar
              else AccessUb UbInvalidScalar
          end
        else AccessUb UbReadUninitialized
    | None => AccessUb UbInvalidLayout
    end.

Definition align_up (offset alignment : nat) : option nat :=
  match alignment with
  | O => None
  | S _ =>
      let remainder := Nat.modulo offset alignment in
      if Nat.eqb remainder 0 then Some offset
      else Some (offset + (alignment - remainder))%nat
  end.

Definition allocation_base_address_memory
    (memory : memory_state) (allocation_id : nat) : option Z :=
  option_map allocation_base (nth_error memory allocation_id).

Definition absolute_pointer_address_memory
    (memory : memory_state) (pointer : pointer_value) : option Z :=
  match pointer_provenance_of pointer with
  | ProvenanceAllocation allocation =>
      match allocation_base_address_memory memory allocation with
      | Some base => Some (base + pointer_address pointer)
      | None => None
      end
  | ProvenanceNone | ProvenanceExposed _ | ProvenanceFunction _ =>
      Some (pointer_address pointer)
  end.

Definition absolute_address_in_allocation_memory
    (memory : memory_state) (allocation_id : nat) (address : Z)
    : option nat :=
  match nth_error memory allocation_id,
      allocation_base_address_memory memory allocation_id with
  | Some allocation, Some base =>
      let relative := address - base in
      if allocation_live allocation && (0 <=? relative) &&
          (relative <=? Z.of_nat (allocation_size allocation)) then
        Some (Z.to_nat relative)
      else None
  | _, _ => None
  end.

Fixpoint find_exposed_allocation_memory
    (memory : memory_state) (exposed : list nat) (address : Z)
    : option (nat * nat) :=
  match exposed with
  | [] => None
  | allocation :: exposed =>
      match absolute_address_in_allocation_memory memory allocation address with
      | Some offset => Some (allocation, offset)
      | None => find_exposed_allocation_memory memory exposed address
      end
  end.

Definition resolve_pointer_allocation_memory
    (memory : memory_state) (pointer : pointer_value) : option (nat * nat) :=
  match pointer_provenance_of pointer with
  | ProvenanceAllocation allocation =>
      if 0 <=? pointer_address pointer then
        Some (allocation, Z.to_nat (pointer_address pointer))
      else None
  | ProvenanceExposed allocations =>
      find_exposed_allocation_memory memory allocations
        (pointer_address pointer)
  | ProvenanceNone | ProvenanceFunction _ => None
  end.

Definition pointer_alignment_memory_result
    (memory : memory_state) (alignment : nat) (pointer : pointer_value)
    : access_result unit :=
  match alignment with
  | O => AccessUb UbInvalidLayout
  | S _ =>
      match absolute_pointer_address_memory memory pointer with
      | Some address =>
          if Z.eqb (Z.modulo address (Z.of_nat alignment)) 0 then AccessOk tt
          else AccessUb UbMisaligned
      | None => AccessUb UbDanglingPointer
      end
  end.

Definition validate_abi_value (layout : type_layout) (value : memory_value)
    : access_result unit :=
  if layout_uninhabited layout then AccessUb UbInvalidScalar
  else
    match layout_abi layout with
    | AbiMemory _ => AccessOk tt
    | AbiScalar scalar =>
        match initialized_scalar_value 0 scalar value with
        | AccessOk _ => AccessOk tt
        | AccessUb reason => AccessUb reason
        | AccessFail => AccessFail
        end
    | AbiScalarPair first second =>
        match initialized_scalar_value 0 first value,
            align_up (scalar_layout_size first)
              (Nat.max 1 (scalar_layout_size second)) with
        | AccessOk _, Some second_offset =>
            match initialized_scalar_value second_offset second value with
            | AccessOk _ => AccessOk tt
            | AccessUb reason => AccessUb reason
            | AccessFail => AccessFail
            end
        | AccessUb reason, _ => AccessUb reason
        | AccessFail, _ | _, None => AccessFail
        end
    end.

Definition write_scalar_bits
    (offset : nat) (scalar : scalar_layout) (bits : Z)
    (target : memory_value) : option memory_value :=
  let size := scalar_layout_size scalar in
  replace_memory_value offset
    (MemoryValue (encode_unsigned size bits) (repeat true size)) target.

Definition encode_variant_tag
    (layout : type_layout) (variant : nat) (target : memory_value)
    : option memory_value :=
  match layout_variants layout with
  | VariantsEmpty => None
  | VariantsSingle expected =>
      if Nat.eqb expected variant then Some target else None
  | VariantsMultiple tag tag_field encoding _ =>
      match layout_field_offset layout tag_field with
      | None => None
      | Some offset =>
          match encoding with
          | TagDirect => write_scalar_bits offset tag (Z.of_nat variant) target
          | TagNiche untagged first last niche_start =>
              if Nat.eqb variant untagged then Some target
              else if Nat.leb first variant && Nat.leb variant last then
                write_scalar_bits offset tag
                  (niche_start + Z.of_nat (variant - first)) target
              else None
          end
      end
  end.

Fixpoint encode_typed_memory_value_with_layouts_fuel
    (fuel : nat) (layouts : layout_env) (shape : value_shape)
    (value : runtime_value) : option memory_value :=
  match fuel with
  | O => None
  | S fuel =>
      let fix encode_fields (parent : value_shape) (variant index : nat)
          (shapes : list value_shape) (values : list runtime_value)
          (target : memory_value) : option memory_value :=
        match shapes, values with
        | [], [] => Some target
        | shape :: shapes, value :: values =>
            match aggregate_field_offset_with_layouts layouts parent variant index,
                encode_typed_memory_value_with_layouts_fuel fuel layouts
                  shape value with
            | Some offset, Some encoded =>
                match replace_memory_value offset encoded target with
                | Some target' =>
                    encode_fields parent variant (S index) shapes values target'
                | None => None
                end
            | _, _ => None
            end
        | _, _ => None
        end in
      match shape, value with
      | expected, VRawAggregate actual bytes init provenance =>
          let raw := MemoryValueWithProvenance bytes init provenance in
          if value_shape_eqb expected actual &&
              memory_value_size_ok
                (shape_size_with_layouts layouts expected) raw then
            Some raw
          else None
      | ShapeTuple shapes, VTuple values =>
          encode_fields shape 0%nat 0%nat shapes values
            (blank_memory_value (shape_size_with_layouts layouts shape))
      | ShapeArray element length, VArray element' values =>
          if value_shape_eqb element element' &&
              Nat.eqb (List.length values) length then
            encode_fields shape 0%nat 0%nat (repeat element length) values
              (blank_memory_value (shape_size_with_layouts layouts shape))
          else None
      | ShapeArray element length, VTuple values =>
          if Nat.eqb (List.length values) length then
            encode_fields shape 0%nat 0%nat (repeat element length) values
              (blank_memory_value (shape_size_with_layouts layouts shape))
          else None
      | ShapeAdtType ty, VUnion declaration active_field field =>
          match ty, find_type_layout layouts ty with
          | TAdt expected_declaration _, Some layout =>
              if String.eqb expected_declaration declaration then
                match layout_fields layout,
                    nth_error (layout_field_types layout) active_field,
                    layout_field_offset layout active_field with
                | FieldsUnion _, Some field_ty, Some offset =>
                    match shape_of_layout_ty field_ty with
                    | Some field_shape =>
                        match encode_typed_memory_value_with_layouts_fuel fuel
                            layouts field_shape field with
                        | Some encoded =>
                            replace_memory_value offset encoded
                              (blank_memory_value (layout_size layout))
                        | None => None
                        end
                    | None => None
                    end
                | _, _, _ => None
                end
              else None
          | _, _ => None
          end
      | ShapeAdtType ty, VAdt declaration variant values =>
          match ty with
          | TAdt expected_declaration _ =>
              if String.eqb expected_declaration declaration then
                match find_type_layout layouts ty with
                | Some layout =>
                    match layout_variant_field_shapes layout variant with
                    | Some shapes =>
                        let target := blank_memory_value (layout_size layout) in
                        match encode_fields shape variant 0%nat shapes values target
                        with
                        | Some target' => encode_variant_tag layout variant target'
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
              else None
          | _ => None
          end
      | ShapeAdt declaration variant shapes,
          VAdt declaration' variant' values =>
          if String.eqb declaration declaration' && Nat.eqb variant variant' then
            let target :=
              blank_memory_value (shape_size_with_layouts layouts shape) in
            match encode_fields shape variant 0%nat shapes values target with
            | Some target' =>
                match find_layout_for_shape layouts shape with
                | Some layout => encode_variant_tag layout variant target'
                | None => encode_typed_memory_value shape value
                end
            | None => None
            end
          else None
      | _, _ => encode_typed_memory_value shape value
      end
  end.

Definition encode_typed_memory_value_with_layouts
    (layouts : layout_env) (shape : value_shape) (value : runtime_value)
    : option memory_value :=
  encode_typed_memory_value_with_layouts_fuel shape_recursion_fuel
    layouts shape value.

Definition value_allocation_with_layouts
    (layouts : layout_env) (value : runtime_value) : allocation :=
  let shape := shape_of_value value in
  match encode_typed_memory_value_with_layouts layouts shape value with
  | Some raw =>
      AllocationWithProvenance
        (shape_size_with_layouts layouts shape)
        (shape_align_with_layouts layouts shape) 0 shape
        (memory_value_bytes raw) (memory_value_init raw)
        (memory_value_provenance raw) true
  | None => Allocation 0 1 0 shape [] [] true
  end.

Definition typed_value_allocation_with_layouts
    (layouts : layout_env) (shape : value_shape) (value : runtime_value)
    : option allocation :=
  if shape_is_unsized shape then None
  else
    match encode_typed_memory_value_with_layouts layouts shape value with
    | Some raw =>
        let size := shape_size_with_layouts layouts shape in
        if memory_value_size_ok size raw then
          Some (AllocationWithProvenance size
            (shape_align_with_layouts layouts shape) 0 shape
            (memory_value_bytes raw) (memory_value_init raw)
            (memory_value_provenance raw) true)
        else None
    | None => None
    end.

Definition read_initialized_scalar_bits
    (offset : nat) (scalar : scalar_layout) (value : memory_value)
    : access_result Z :=
  let size := scalar_layout_size scalar in
  match slice_memory_value offset size value with
  | Some raw =>
      if all_initialized (memory_value_init raw) then
        AccessOk (decode_unsigned (memory_value_bytes raw))
      else AccessUb UbReadUninitialized
  | None => AccessUb UbInvalidLayout
  end.

Definition decode_variant_index
    (layout : type_layout) (value : memory_value) : access_result nat :=
  match layout_variants layout with
  | VariantsEmpty => AccessUb UbInvalidEnumTag
  | VariantsSingle variant => AccessOk variant
  | VariantsMultiple tag tag_field encoding _ =>
      match layout_field_offset layout tag_field with
      | None => AccessUb UbInvalidLayout
      | Some offset =>
          match read_initialized_scalar_bits offset tag value with
          | AccessOk bits =>
              match encoding with
              | TagDirect =>
                  if scalar_in_valid_range tag bits then
                    AccessOk (Z.to_nat bits)
                  else AccessUb UbInvalidEnumTag
              | TagNiche untagged first last niche_start =>
                  let delta := Z.modulo (bits - niche_start)
                    (scalar_modulus tag) in
                  let span := Z.of_nat (last - first) in
                  if (0 <=? delta) && (delta <=? span) then
                    AccessOk (first + Z.to_nat delta)%nat
                  else AccessOk untagged
              end
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
      end
  end.

Fixpoint decode_typed_memory_value_with_layouts_fuel
    (fuel : nat) (layouts : layout_env) (shape : value_shape)
    (value : memory_value) : access_result runtime_value :=
  match fuel with
  | O => AccessFail
  | S fuel =>
      let fix decode_fields (parent : value_shape) (variant index : nat)
          (shapes : list value_shape) : access_result (list runtime_value) :=
        match shapes with
        | [] => AccessOk []
        | shape :: shapes =>
            match aggregate_field_offset_with_layouts layouts parent variant index
            with
            | Some offset =>
                let size := shape_size_with_layouts layouts shape in
                match slice_memory_value offset size value with
                | Some field_value =>
                    match decode_typed_memory_value_with_layouts_fuel fuel
                            layouts shape field_value,
                        decode_fields parent variant (S index) shapes with
                    | AccessOk field, AccessOk fields =>
                        AccessOk (field :: fields)
                    | AccessUb reason, _ | _, AccessUb reason =>
                        AccessUb reason
                    | AccessFail, _ | _, AccessFail => AccessFail
                    end
                | None => AccessUb UbInvalidLayout
                end
            | None => AccessUb UbInvalidLayout
            end
        end in
      let expected_size := shape_size_with_layouts layouts shape in
      if negb (memory_value_size_ok expected_size value) then
        AccessUb UbInvalidLayout
      else
        match shape with
        | ShapeTuple fields =>
            match decode_fields shape 0%nat 0%nat fields with
            | AccessOk values => AccessOk (VTuple values)
            | AccessUb reason => AccessUb reason
            | AccessFail => AccessFail
            end
        | ShapeArray element length =>
            match decode_fields shape 0%nat 0%nat (repeat element length) with
            | AccessOk values => AccessOk (VArray element values)
            | AccessUb reason => AccessUb reason
            | AccessFail => AccessFail
            end
        | ShapeAdtType ty =>
            match ty, find_type_layout layouts ty with
            | TAdt declaration _, Some layout =>
                match layout_fields layout with
                | FieldsUnion _ =>
                    if valid_bytes (memory_value_bytes value) &&
                        raw_provenance_init_consistent
                          (memory_value_init value)
                          (memory_value_provenance value) then
                      AccessOk (VRawAggregate shape
                        (memory_value_bytes value) (memory_value_init value)
                        (memory_value_provenance value))
                    else AccessUb UbInvalidLayout
                | _ =>
                    match decode_variant_index layout value with
                    | AccessOk actual_variant =>
                        match layout_variant layout actual_variant,
                            layout_variant_field_shapes layout actual_variant with
                        | Some variant_layout, Some fields =>
                            if variant_uninhabited variant_layout then
                              AccessUb UbInvalidEnumTag
                            else
                              match decode_fields shape actual_variant 0%nat fields
                              with
                              | AccessOk values =>
                                  match validate_abi_value layout value with
                                  | AccessOk _ =>
                                      AccessOk
                                        (VAdt declaration actual_variant values)
                                  | AccessUb reason => AccessUb reason
                                  | AccessFail => AccessFail
                                  end
                              | AccessUb reason => AccessUb reason
                              | AccessFail => AccessFail
                              end
                        | _, _ => AccessUb UbInvalidLayout
                        end
                    | AccessUb reason => AccessUb reason
                    | AccessFail => AccessFail
                    end
                end
            | _, _ => AccessUb UbInvalidLayout
            end
        | ShapeAdt declaration expected_variant fields =>
            match find_layout_for_shape layouts shape with
            | Some layout =>
                match decode_variant_index layout value with
                | AccessOk actual_variant =>
                    if Nat.eqb actual_variant expected_variant then
                      match layout_variant layout actual_variant with
                      | Some variant_layout =>
                          if variant_uninhabited variant_layout then
                            AccessUb UbInvalidEnumTag
                          else
                            match decode_fields shape actual_variant 0%nat fields with
                            | AccessOk values =>
                                match validate_abi_value layout value with
                                | AccessOk _ =>
                                    AccessOk
                                      (VAdt declaration actual_variant values)
                                | AccessUb reason => AccessUb reason
                                | AccessFail => AccessFail
                                end
                            | AccessUb reason => AccessUb reason
                            | AccessFail => AccessFail
                            end
                      | None => AccessUb UbInvalidEnumTag
                      end
                    else AccessUb UbInvalidEnumTag
                | AccessUb reason => AccessUb reason
                | AccessFail => AccessFail
                end
            | None =>
                if all_initialized (memory_value_init value) then
                  match decode_value_with_provenance shape value with
                  | Some decoded => AccessOk decoded
                  | None => AccessUb UbInvalidEnumTag
                  end
                else AccessUb UbReadUninitialized
            end
        | ShapeSlice _ | ShapeStr => AccessUb UbInvalidMetadata
        | _ =>
            if all_initialized (memory_value_init value) then
              match decode_value_with_provenance shape value with
              | Some decoded =>
                  match find_layout_for_shape layouts shape with
                  | Some layout =>
                      match validate_abi_value layout value with
                      | AccessOk _ => AccessOk decoded
                      | AccessUb reason => AccessUb reason
                      | AccessFail => AccessFail
                      end
                  | None => AccessOk decoded
                  end
              | None => AccessUb UbInvalidScalar
              end
            else AccessUb UbReadUninitialized
        end
  end.

Definition decode_typed_memory_value_with_layouts
    (layouts : layout_env) (shape : value_shape) (value : memory_value)
    : access_result runtime_value :=
  decode_typed_memory_value_with_layouts_fuel shape_recursion_fuel
    layouts shape value.

Definition memory_range_result_with_layouts
    (layouts : layout_env)
    (policy_check : nat -> nat -> operation_type -> bool)
    (allocation_id offset : nat) (allocation : allocation)
    (operation : operation_type) : access_result unit :=
  let layout := operation_type_layout_with_layouts layouts operation in
  let size := operation_layout_size layout in
  let align := operation_layout_align layout in
  if negb (policy_check allocation_id offset operation) then
    AccessUb UbInvalidDeref
  else if negb (allocation_live allocation) then
    AccessUb UbUseAfterFree
  else if Nat.eqb align 0 then
    AccessUb UbInvalidLayout
  else if negb (Nat.leb (offset + size) (allocation_size allocation)) then
    AccessUb UbOutOfBounds
  else if negb (range_available offset size (allocation_bytes allocation)) then
    AccessUb UbOutOfBounds
  else if negb (range_available offset size (allocation_init allocation)) then
    AccessUb UbOutOfBounds
  else if negb
      (range_available offset size (allocation_provenance allocation)) then
    AccessUb UbOutOfBounds
  else if negb (Nat.leb align (allocation_align allocation)) then
    AccessUb UbMisaligned
  else if negb (aligned_offset offset align) then
    AccessUb UbMisaligned
  else AccessOk tt.

Definition memory_range_result
    (policy_check : nat -> nat -> operation_type -> bool)
    (allocation_id offset : nat) (allocation : allocation)
    (operation : operation_type) : access_result unit :=
  memory_range_result_with_layouts [] policy_check allocation_id offset
    allocation operation.

Definition mem_cast_result_with_layouts
    (layouts : layout_env) (value : memory_value) (operation : operation_type)
    : access_result operation_value :=
  let layout := operation_type_layout_with_layouts layouts operation in
  if Nat.eqb (List.length (memory_value_bytes value))
      (operation_layout_size layout) &&
      Nat.eqb (List.length (memory_value_init value))
        (operation_layout_size layout) &&
      Nat.eqb (List.length (memory_value_provenance value))
        (operation_layout_size layout) then
    match operation with
    | TypedOp shape =>
        match decode_typed_memory_value_with_layouts layouts shape value with
        | AccessOk decoded => AccessOk (OVTyped decoded)
        | AccessUb reason => AccessUb reason
        | AccessFail => AccessFail
        end
    | UntypedOp raw_layout => AccessOk (OVUntyped raw_layout value)
    end
  else AccessUb UbInvalidLayout.

Definition mem_cast_result (value : memory_value) (operation : operation_type)
    : access_result operation_value :=
  mem_cast_result_with_layouts [] value operation.

Definition memory_access_result_with_layouts
    (layouts : layout_env)
    (policy_check : nat -> nat -> operation_type -> bool)
    (memory : memory_state) (allocation_id offset : nat)
    (operation : operation_type) : access_result unit :=
  match nth_error memory allocation_id with
  | Some allocation =>
      memory_range_result_with_layouts layouts policy_check allocation_id offset
        allocation operation
  | None => AccessUb UbDanglingPointer
  end.

Definition memory_access_result
    (policy_check : nat -> nat -> operation_type -> bool)
    (memory : memory_state) (allocation_id offset : nat)
    (operation : operation_type) : access_result unit :=
  memory_access_result_with_layouts [] policy_check memory allocation_id offset
    operation.

Definition reference_target_operation
    (layouts : layout_env) (pointee : value_shape) (pointer : pointer_value)
    : option operation_type :=
  match pointee, pointer_metadata_of pointer with
  | ShapeSlice element, PointerLength length =>
      Some (UntypedOp
        (repeat_operation_layout
          (layout_of_shape_with_layouts layouts element) length))
  | ShapeStr, PointerLength length =>
      Some (UntypedOp (OperationLayout length 1%nat))
  | ShapeSlice _, _ | ShapeStr, _ => None
  | _, PointerThin => Some (TypedOp pointee)
  | _, _ => None
  end.

Definition validate_reference_target
    (layouts : layout_env) (memory : memory_state)
    (pointee : value_shape) (pointer : pointer_value)
    : access_result unit :=
  match absolute_pointer_address_memory memory pointer with
  | Some address =>
      if Z.eqb address 0 then AccessUb UbInvalidPointerProvenance
      else
        match reference_target_operation layouts pointee pointer with
        | None => AccessUb UbInvalidMetadata
        | Some operation =>
            let operation_layout :=
              operation_type_layout_with_layouts layouts operation in
            let size := operation_layout_size operation_layout in
            let align := operation_layout_align operation_layout in
            if Nat.eqb size 0 then
              pointer_alignment_memory_result memory align pointer
            else
              match resolve_pointer_allocation_memory memory pointer with
              | Some (allocation, offset) =>
                  memory_access_result_with_layouts layouts
                    (policy_may_read permissive_memory_policy)
                    memory allocation offset operation
              | None => AccessUb UbInvalidPointerProvenance
              end
        end
  | None => AccessUb UbDanglingPointer
  end.

Fixpoint validate_loaded_references_fuel
    (fuel : nat) (layouts : layout_env) (memory : memory_state)
    (shape : value_shape) (value : runtime_value) : access_result unit :=
  match fuel with
  | O => AccessFail
  | S fuel =>
      let fix validate_values
          (shapes : list value_shape) (values : list runtime_value)
          : access_result unit :=
        match shapes, values with
        | [], [] => AccessOk tt
        | shape :: shapes, value :: values =>
            access_bind
              (validate_loaded_references_fuel fuel layouts memory shape value)
              (fun _ => validate_values shapes values)
        | _, _ => AccessFail
        end in
      match shape, value with
      | ShapeReference _ pointee, VPointerValue pointee' pointer =>
          if value_shape_eqb pointee pointee' then
            validate_reference_target layouts memory pointee pointer
          else AccessFail
      | ShapeArray element length, VArray element' values =>
          if value_shape_eqb element element' &&
              Nat.eqb (List.length values) length then
            validate_values (repeat element length) values
          else AccessFail
      | ShapeArray element length, VTuple values =>
          if Nat.eqb (List.length values) length then
            validate_values (repeat element length) values
          else AccessFail
      | ShapeTuple shapes, VTuple values => validate_values shapes values
      | ShapeAdtType ty, VAdt declaration variant values =>
          match ty, find_type_layout layouts ty with
          | TAdt expected_declaration _, Some layout =>
              if String.eqb expected_declaration declaration then
                match layout_variant_field_shapes layout variant with
                | Some shapes => validate_values shapes values
                | None => AccessFail
                end
              else AccessFail
          | _, _ => AccessFail
          end
      | ShapeAdtType ty, VUnion declaration active_field field =>
          match ty, find_type_layout layouts ty with
          | TAdt expected_declaration _, Some layout =>
              if String.eqb expected_declaration declaration then
                match layout_fields layout,
                    nth_error (layout_field_types layout) active_field with
                | FieldsUnion _, Some field_ty =>
                    match shape_of_layout_ty field_ty with
                    | Some field_shape =>
                        validate_loaded_references_fuel fuel layouts memory
                          field_shape field
                    | None => AccessFail
                    end
                | _, _ => AccessFail
                end
              else AccessFail
          | _, _ => AccessFail
          end
      | ShapeAdtType ty, VRawAggregate (ShapeAdtType ty') _ _ _ =>
          if ty_eqb ty ty' then AccessOk tt else AccessFail
      | ShapeAdt declaration variant shapes,
          VAdt declaration' variant' values =>
          if String.eqb declaration declaration' && Nat.eqb variant variant'
          then validate_values shapes values
          else AccessFail
      | ShapePointer pointee, VPointerValue pointee' _
      | ShapeRawPointer _ pointee, VPointerValue pointee' _ =>
          if value_shape_eqb pointee pointee' then AccessOk tt else AccessFail
      | ShapeUnit, VUnit | ShapeBool, VBool _ | ShapeChar, VChar _
      | ShapeFloat _, VFloatBits _ _ | ShapeBits _, VBits _ _ => AccessOk tt
      | _, _ => AccessFail
      end
  end.

Definition validate_loaded_references
    (layouts : layout_env) (memory : memory_state)
    (shape : value_shape) (value : runtime_value) : access_result unit :=
  validate_loaded_references_fuel shape_recursion_fuel layouts memory shape value.

Definition read_allocation_operation_result_with_layouts
    (layouts : layout_env) (memory : memory_state)
    (allocation_id offset : nat) (operation : operation_type)
    : access_result operation_value :=
  match nth_error memory allocation_id with
  | Some allocation =>
      match memory_range_result_with_layouts layouts
          (policy_may_read permissive_memory_policy) allocation_id offset
          allocation operation with
      | AccessOk _ =>
        let size :=
          operation_layout_size
            (operation_type_layout_with_layouts layouts operation) in
        mem_cast_result_with_layouts layouts
          (MemoryValueWithProvenance
            (firstn size (skipn offset (allocation_bytes allocation)))
            (firstn size (skipn offset (allocation_init allocation)))
            (firstn size (skipn offset
              (allocation_provenance allocation))))
          operation
      | AccessUb reason => AccessUb reason
      | AccessFail => AccessFail
      end
  | None => AccessUb UbDanglingPointer
  end.

Definition read_allocation_operation_result (memory : memory_state)
    (allocation_id offset : nat) (operation : operation_type)
    : access_result operation_value :=
  read_allocation_operation_result_with_layouts [] memory allocation_id offset
    operation.

Definition read_allocation_result_with_layouts
    (layouts : layout_env) (memory : memory_state)
    (allocation_id offset : nat) (shape : value_shape)
    : access_result runtime_value :=
  match read_allocation_operation_result_with_layouts layouts memory
      allocation_id offset
      (TypedOp shape) with
  | AccessOk (OVTyped value) =>
      match validate_loaded_references layouts memory shape value with
      | AccessOk _ => AccessOk value
      | AccessUb reason => AccessUb reason
      | AccessFail => AccessFail
      end
  | AccessOk (OVUntyped _ _) => AccessFail
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition read_allocation_result (memory : memory_state)
    (allocation_id offset : nat) (shape : value_shape)
    : access_result runtime_value :=
  read_allocation_result_with_layouts [] memory allocation_id offset shape.

Definition read_allocation (memory : memory_state) (allocation_id offset : nat)
    (shape : value_shape) : option runtime_value :=
  match read_allocation_result memory allocation_id offset shape with
  | AccessOk value => Some value
  | _ => None
  end.

Definition encode_operation_value_as_with_layouts
    (layouts : layout_env) (operation : operation_type)
    (value : operation_value) : option memory_value :=
  match operation, value with
  | TypedOp shape, OVTyped typed_value =>
      encode_typed_memory_value_with_layouts layouts shape typed_value
  | UntypedOp layout, OVUntyped value_layout raw_value =>
      if operation_layout_eqb layout value_layout &&
          Nat.eqb (List.length (memory_value_bytes raw_value))
            (operation_layout_size layout) &&
          Nat.eqb (List.length (memory_value_init raw_value))
            (operation_layout_size layout) &&
          Nat.eqb (List.length (memory_value_provenance raw_value))
            (operation_layout_size layout) then Some raw_value
      else None
  | _, _ => None
  end.

Definition encode_operation_value_as (operation : operation_type)
    (value : operation_value) : option memory_value :=
  encode_operation_value_as_with_layouts [] operation value.

Definition validate_operation_value_references
    (layouts : layout_env) (memory : memory_state)
    (operation : operation_type) (value : operation_value)
    : access_result unit :=
  match operation, value with
  | TypedOp shape, OVTyped typed_value =>
      if negb (valid_runtime_value typed_value) then AccessUb UbInvalidScalar
      else
        match encode_typed_memory_value_with_layouts layouts shape typed_value with
        | Some raw =>
            match decode_typed_memory_value_with_layouts layouts shape raw with
            | AccessOk _ =>
                match validate_loaded_references layouts memory shape typed_value with
                | AccessOk _ => AccessOk tt
                | AccessUb reason => AccessUb reason
                | AccessFail => AccessUb UbInvalidLayout
                end
            | AccessUb reason => AccessUb reason
            | AccessFail => AccessUb UbInvalidLayout
            end
        | None => AccessUb UbInvalidLayout
        end
  | UntypedOp _, OVUntyped _ _ => AccessOk tt
  | _, _ => AccessFail
  end.

Definition write_allocation_operation_result_with_layouts
    (layouts : layout_env) (memory : memory_state)
    (allocation_id offset : nat) (operation : operation_type)
    (value : operation_value) : access_result memory_state :=
  match validate_operation_value_references layouts memory operation value with
  | AccessOk _ =>
      match nth_error memory allocation_id,
          encode_operation_value_as_with_layouts layouts operation value with
      | Some allocation, Some raw_value =>
          match memory_range_result_with_layouts layouts
              (policy_may_write permissive_memory_policy) allocation_id offset
              allocation operation with
          | AccessOk _ =>
            let size :=
              operation_layout_size
                (operation_type_layout_with_layouts layouts operation) in
            let bytes' :=
              (firstn offset (allocation_bytes allocation) ++
              memory_value_bytes raw_value ++
              skipn (offset + size) (allocation_bytes allocation))%list in
            let init' :=
              (firstn offset (allocation_init allocation) ++
              memory_value_init raw_value ++
              skipn (offset + size) (allocation_init allocation))%list in
            let provenance' :=
              (firstn offset (allocation_provenance allocation) ++
              memory_value_provenance raw_value ++
              skipn (offset + size)
                (allocation_provenance allocation))%list in
            match set_nth allocation_id
                (AllocationWithProvenance (allocation_size allocation)
                  (allocation_align allocation) (allocation_base allocation)
                  (allocation_shape allocation) bytes' init'
                  provenance'
                  (allocation_live allocation))
                memory with
            | Some memory' => AccessOk memory'
            | None => AccessFail
            end
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
      | None, _ => AccessUb UbDanglingPointer
      | _, None => AccessFail
      end
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition write_allocation_operation_result (memory : memory_state)
    (allocation_id offset : nat) (operation : operation_type)
    (value : operation_value) : access_result memory_state :=
  write_allocation_operation_result_with_layouts [] memory allocation_id offset
    operation value.

Definition read_allocation_untyped_result (memory : memory_state)
    (allocation_id offset : nat) (layout : operation_layout)
    : access_result operation_value :=
  read_allocation_operation_result memory allocation_id offset
    (UntypedOp layout).

Definition write_allocation_untyped_result (memory : memory_state)
    (allocation_id offset : nat) (layout : operation_layout)
    (value : memory_value) : access_result memory_state :=
  write_allocation_operation_result memory allocation_id offset
    (UntypedOp layout) (OVUntyped layout value).

Definition write_allocation (memory : memory_state) (allocation_id offset : nat)
    (shape : value_shape) (value : runtime_value) : option memory_state :=
  match write_allocation_operation_result memory allocation_id offset
      (TypedOp shape) (OVTyped value) with
  | AccessOk memory' => Some memory'
  | AccessUb _ | AccessFail => None
  end.

Definition write_allocation_with_layouts (layouts : layout_env)
    (memory : memory_state) (allocation_id offset : nat)
    (shape : value_shape) (value : runtime_value) : option memory_state :=
  match write_allocation_operation_result_with_layouts layouts memory
      allocation_id offset (TypedOp shape) (OVTyped value) with
  | AccessOk memory' => Some memory'
  | AccessUb _ | AccessFail => None
  end.

Section Addresses.

Context `{Addr : AddrAlg}.

Definition append_allocation (memory : memory_state) (a : allocation)
    : option (nat * memory_state) :=
  match choose_base memory (allocation_size a) (allocation_align a) with
  | Some base => Some (length memory, (memory ++ [with_base a base])%list)
  | None => None
  end.

Definition allocate_value (memory : memory_state) (value : runtime_value)
    : option (nat * memory_state) :=
  match encode_value value with
  | Some _ => append_allocation memory (value_allocation value)
  | None => None
  end.

Definition allocate_value_with_layouts
    (layouts : layout_env) (memory : memory_state) (value : runtime_value)
    : option (nat * memory_state) :=
  let allocation := value_allocation_with_layouts layouts value in
  if Nat.eqb (allocation_size allocation)
      (shape_size_with_layouts layouts (allocation_shape allocation)) then
    append_allocation memory allocation
  else None.

Definition allocate_typed_value_with_layouts (layouts : layout_env)
    (memory : memory_state) (shape : value_shape) (value : runtime_value)
    : option (nat * memory_state) :=
  match typed_value_allocation_with_layouts layouts shape value with
  | Some a => append_allocation memory a
  | None => None
  end.

Definition uninitialized_allocation_with_layouts
    (layouts : layout_env) (shape : value_shape) : option allocation :=
  if shape_is_unsized shape then None
  else
    let size := shape_size_with_layouts layouts shape in
    Some (AllocationWithProvenance size
      (shape_align_with_layouts layouts shape) 0 shape
      (repeat 0 size) (repeat false size) (repeat None size) true).

Definition allocate_uninitialized_with_layouts
    (layouts : layout_env) (memory : memory_state) (shape : value_shape)
    : option (nat * memory_state) :=
  match uninitialized_allocation_with_layouts layouts shape with
  | Some allocation => append_allocation memory allocation
  | None => None
  end.

Definition deinitialize_allocation (memory : memory_state)
    (allocation_id offset length : nat) : option memory_state :=
  match nth_error memory allocation_id with
  | Some allocation =>
      if allocation_live allocation &&
          range_available offset length (allocation_init allocation) then
        let init' :=
          (firstn offset (allocation_init allocation) ++ repeat false length ++
          skipn (offset + length) (allocation_init allocation))%list in
        let provenance' :=
          (firstn offset (allocation_provenance allocation) ++
          repeat None length ++
          skipn (offset + length) (allocation_provenance allocation))%list in
        set_nth allocation_id
          (AllocationWithProvenance
            (allocation_size allocation) (allocation_align allocation)
            (allocation_base allocation)
            (allocation_shape allocation) (allocation_bytes allocation) init'
            provenance'
            (allocation_live allocation))
          memory
      else None
  | None => None
  end.

Definition kill_allocation (memory : memory_state) (allocation_id : nat)
    : option memory_state :=
  match nth_error memory allocation_id with
  | Some allocation =>
      set_nth allocation_id
        (AllocationWithProvenance
          (allocation_size allocation) (allocation_align allocation)
          (allocation_base allocation)
          (allocation_shape allocation) (allocation_bytes allocation)
          (repeat false (allocation_size allocation))
          (repeat None (allocation_size allocation)) false)
        memory
  | None => None
  end.

Definition read_allocation_value (memory : memory_state) (allocation_id : nat)
    : option runtime_value :=
  match nth_error memory allocation_id with
  | Some allocation =>
      read_allocation memory allocation_id 0 (allocation_shape allocation)
  | None => None
  end.

Definition write_allocation_value (memory : memory_state) (allocation_id : nat)
    (value : runtime_value) : option memory_state :=
  match nth_error memory allocation_id with
  | Some allocation =>
      write_allocation memory allocation_id 0 (allocation_shape allocation) value
  | None => None
  end.

Record prog_state := ByteStateData {
  state_locals : list local_storage;
  state_memory : memory_state;
  state_exposed_allocations : list nat;
}.

Definition ByteState (locals : list local_storage) (memory : memory_state)
    : prog_state := ByteStateData locals memory [].

Definition ByteStateWithExposed
    (locals : list local_storage) (memory : memory_state)
    (exposed : list nat) : prog_state :=
  ByteStateData locals memory exposed.

Fixpoint initialize_locals (locals : list slot) (memory : memory_state)
    : list local_storage * memory_state :=
  match locals with
  | [] => ([], memory)
  | Dead :: locals =>
      let '(storages, memory') := initialize_locals locals memory in
      (LocalDead :: storages, memory')
  | Uninit :: locals =>
      let '(storages, memory') := initialize_locals locals memory in
      (LocalUnallocated :: storages, memory')
  | Init value :: locals =>
      match append_allocation memory (value_allocation value) with
      | Some (allocation_id, memory') =>
          let '(storages, memory'') := initialize_locals locals memory' in
          (LocalAllocated allocation_id :: storages, memory'')
      | None =>
          let '(storages, memory') := initialize_locals locals memory in
          (LocalUnallocated :: storages, memory')
      end
  end.

Definition ProgState (locals : list slot) (memory : memory_state) : prog_state :=
  let '(storages, memory') := initialize_locals locals memory in
  ByteState storages memory'.

Definition ProgramState := ProgState.

Definition state_with_locals (state : prog_state) (locals : list local_storage)
    : prog_state :=
  ByteStateWithExposed locals (state_memory state)
    (state_exposed_allocations state).

Definition state_with_memory (state : prog_state) (memory : memory_state)
    : prog_state :=
  ByteStateWithExposed (state_locals state) memory
    (state_exposed_allocations state).

Definition state_with_locals_memory (state : prog_state)
    (locals : list local_storage)
    (memory : memory_state) : prog_state :=
  ByteStateWithExposed locals memory (state_exposed_allocations state).

Definition state_with_exposed_allocations
    (state : prog_state) (exposed : list nat) : prog_state :=
  ByteStateWithExposed (state_locals state) (state_memory state) exposed.

Definition add_exposed_allocation (allocation : nat) (exposed : list nat)
    : list nat :=
  if existsb (Nat.eqb allocation) exposed then exposed
  else allocation :: exposed.

Definition allocation_base_address
    (memory : memory_state) (allocation_id : nat) : option Z :=
  allocation_base_address_memory memory allocation_id.

Definition absolute_address_of_pointer
    (memory : memory_state) (pointer : pointer_value) : option Z :=
  absolute_pointer_address_memory memory pointer.

Definition pointer_address_in_range (address : Z) : bool :=
  (0 <=? address) &&
  (address <? 2 ^ Z.of_nat (8 * pointer_bytes)%nat).

Definition pointer_alignment_result
    (alignment : nat) (pointer : pointer_value) (state : prog_state)
    : access_result unit :=
  pointer_alignment_memory_result (state_memory state) alignment pointer.

Definition expose_pointer_provenance
    (pointee : value_shape) (pointer : pointer_value) (state : prog_state)
    : access_result (runtime_value * prog_state) :=
  match absolute_address_of_pointer (state_memory state) pointer with
  | None => AccessUb UbDanglingPointer
  | Some address =>
      if negb (pointer_address_in_range address) then
        AccessUb UbPointerArithmeticOverflow
      else
        match pointer_provenance_of pointer with
        | ProvenanceAllocation allocation =>
            match nth_error (state_memory state) allocation with
            | Some target =>
                if allocation_live target then
                  AccessOk (VBits WSize address,
                    state_with_exposed_allocations state
                      (add_exposed_allocation allocation
                        (state_exposed_allocations state)))
                else AccessUb UbUseAfterFree
            | None => AccessUb UbDanglingPointer
            end
        | ProvenanceNone | ProvenanceExposed _ =>
            AccessOk (VBits WSize address, state)
        | ProvenanceFunction _ =>
            AccessOk (VBits WSize address, state)
        end
  end.

Definition absolute_address_in_allocation
    (memory : memory_state) (allocation_id : nat) (address : Z)
    : option nat :=
  absolute_address_in_allocation_memory memory allocation_id address.

Definition find_exposed_allocation
    (memory : memory_state) (exposed : list nat) (address : Z)
    : option (nat * nat) :=
  find_exposed_allocation_memory memory exposed address.

Definition pointer_with_exposed_provenance
    (pointee : value_shape) (address : Z) (metadata : pointer_metadata)
    (state : prog_state) : runtime_value :=
  match state_exposed_allocations state with
  | [] => VPointerValue pointee
      (PointerValue ProvenanceNone address metadata)
  | allocations => VPointerValue pointee
      (PointerValue (ProvenanceExposed allocations) address metadata)
  end.

Definition pointer_with_exposed_provenance_result
    (pointee : value_shape) (address : Z) (metadata : pointer_metadata)
    (state : prog_state) : access_result runtime_value :=
  if pointer_address_in_range address then
    AccessOk (pointer_with_exposed_provenance pointee address metadata state)
  else AccessUb UbPointerArithmeticOverflow.

Definition pointer_without_provenance
    (pointee : value_shape) (address : Z) (metadata : pointer_metadata)
    : runtime_value :=
  VPointerValue pointee (PointerValue ProvenanceNone address metadata).

Definition resolve_pointer_allocation
    (state : prog_state) (pointer : pointer_value) : option (nat * nat) :=
  resolve_pointer_allocation_memory (state_memory state) pointer.

Definition pointer_with_address_in_state
    (pointer : pointer_value) (address : Z) (state : prog_state)
    : pointer_value :=
  match pointer_provenance_of pointer with
  | ProvenanceAllocation allocation =>
      match allocation_base_address (state_memory state) allocation with
      | Some base => PointerValue (ProvenanceAllocation allocation)
          (address - base) (pointer_metadata_of pointer)
      | None => PointerValue (ProvenanceAllocation allocation)
          (pointer_address pointer) (pointer_metadata_of pointer)
      end
  | provenance =>
      PointerValue provenance address (pointer_metadata_of pointer)
  end.

Definition offset_pointer_inbounds
    (pointer : pointer_value) (delta : Z) (state : prog_state)
    : access_result pointer_value :=
  match pointer_provenance_of pointer with
  | ProvenanceAllocation allocation =>
      match nth_error (state_memory state) allocation with
      | Some target =>
          if allocation_live target then
            let offset := pointer_address pointer + delta in
            if (0 <=? offset) &&
                (offset <=? Z.of_nat (allocation_size target)) then
              AccessOk (PointerValue (ProvenanceAllocation allocation)
                offset (pointer_metadata_of pointer))
            else AccessUb UbOutOfBounds
          else AccessUb UbUseAfterFree
      | None => AccessUb UbDanglingPointer
      end
  | ProvenanceExposed allocations =>
      match find_exposed_allocation (state_memory state) allocations
          (pointer_address pointer) with
      | Some (allocation, current_offset) =>
          match nth_error (state_memory state) allocation with
          | Some target =>
              let offset := Z.of_nat current_offset + delta in
              if (0 <=? offset) &&
                  (offset <=? Z.of_nat (allocation_size target)) then
                AccessOk (PointerValue (ProvenanceAllocation allocation)
                  offset (pointer_metadata_of pointer))
              else AccessUb UbOutOfBounds
          | None => AccessUb UbDanglingPointer
          end
      | None => AccessUb UbInvalidPointerProvenance
      end
  | ProvenanceNone => AccessUb UbInvalidPointerProvenance
  | ProvenanceFunction _ => AccessUb UbInvalidPointerProvenance
  end.

Definition wrapping_offset_pointer
    (pointer : pointer_value) (delta : Z) : pointer_value :=
  PointerValue (pointer_provenance_of pointer)
    (Z.modulo (pointer_address pointer + delta)
      (2 ^ Z.of_nat (8 * pointer_bytes)%nat))
    (pointer_metadata_of pointer).

Definition read_through_pointer_result
    (layouts : layout_env) (pointee : value_shape) (pointer : pointer_value)
    (state : prog_state) : access_result runtime_value :=
  if shape_is_unsized pointee then AccessUb UbInvalidMetadata
  else if Nat.eqb (shape_size_with_layouts layouts pointee) 0 then
    match pointer_alignment_result
        (shape_align_with_layouts layouts pointee) pointer state with
    | AccessOk _ =>
        decode_typed_memory_value_with_layouts layouts pointee
          (MemoryValue [] [])
    | AccessUb reason => AccessUb reason
    | AccessFail => AccessFail
    end
  else
    match resolve_pointer_allocation state pointer with
    | Some (allocation, offset) =>
        read_allocation_result_with_layouts layouts (state_memory state)
          allocation offset pointee
    | None => AccessUb UbInvalidPointerProvenance
    end.

Definition write_through_pointer_result
    (layouts : layout_env) (pointee : value_shape) (pointer : pointer_value)
    (value : runtime_value) (state : prog_state) : access_result prog_state :=
  if shape_is_unsized pointee then AccessUb UbInvalidMetadata
  else if Nat.eqb (shape_size_with_layouts layouts pointee) 0 then
    match encode_typed_memory_value_with_layouts layouts pointee value with
    | Some raw =>
        if memory_value_size_ok 0 raw then
          match pointer_alignment_result
              (shape_align_with_layouts layouts pointee) pointer state with
          | AccessOk _ => AccessOk state
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
        else AccessUb UbInvalidLayout
    | None => AccessFail
    end
  else
    match resolve_pointer_allocation state pointer with
    | Some (allocation, offset) =>
        match write_allocation_operation_result_with_layouts layouts
            (state_memory state) allocation offset (TypedOp pointee)
            (OVTyped value) with
        | AccessOk memory => AccessOk (state_with_memory state memory)
        | AccessUb reason => AccessUb reason
        | AccessFail => AccessFail
        end
    | None => AccessUb UbInvalidPointerProvenance
    end.

Fixpoint power_of_two_fuel (fuel value : nat) : bool :=
  match fuel with
  | O => false
  | S fuel =>
      match value with
      | O => false
      | 1%nat => true
      | _ => Nat.even value && power_of_two_fuel fuel (Nat.div2 value)
      end
  end.

Definition is_power_of_two (value : nat) : bool :=
  power_of_two_fuel (S value) value.

Fixpoint initialized_provenance_wf
    (allocation_count : nat) (init : list bool)
    (provenance : list (option pointer_provenance)) : bool :=
  match init, provenance with
  | [], [] => true
  | initialized :: init, tag :: provenance =>
      let tag_wf :=
        match tag with
        | None => true
        | Some ProvenanceNone => false
        | Some (ProvenanceAllocation allocation) =>
            initialized && Nat.ltb allocation allocation_count
        | Some (ProvenanceExposed allocations) =>
            initialized &&
            match allocations with
            | [] => false
            | _ => forallb (fun allocation =>
                Nat.ltb allocation allocation_count) allocations
            end
        | Some (ProvenanceFunction definition) =>
            initialized && negb (String.eqb definition EmptyString)
        end in
      tag_wf && initialized_provenance_wf allocation_count init provenance
  | _, _ => false
  end.

Definition allocation_structure_wf (allocation_count : nat)
    (allocation : allocation) : bool :=
  let size := allocation_size allocation in
  let align := allocation_align allocation in
  Nat.eqb (List.length (allocation_bytes allocation)) size &&
  Nat.eqb (List.length (allocation_init allocation)) size &&
  Nat.eqb (List.length (allocation_provenance allocation)) size &&
  valid_bytes (allocation_bytes allocation) &&
  is_power_of_two align &&
  negb (shape_is_unsized (allocation_shape allocation)) &&
  initialized_provenance_wf allocation_count
    (allocation_init allocation) (allocation_provenance allocation) &&
  (allocation_live allocation ||
    (negb (existsb (fun initialized => initialized)
      (allocation_init allocation)) &&
     forallb (fun tag =>
       match tag with None => true | Some _ => false end)
       (allocation_provenance allocation))).

Definition allocation_layout_wf (layouts : layout_env) (allocation : allocation) : bool :=
  negb (allocation_live allocation) ||
    (shape_layout_supported layouts (allocation_shape allocation) &&
     Nat.eqb (shape_size_with_layouts layouts (allocation_shape allocation))
       (allocation_size allocation) &&
     Nat.leb (shape_align_with_layouts layouts (allocation_shape allocation))
       (allocation_align allocation)).

Definition allocation_wf
    (layouts : layout_env) (allocation_count : nat)
    (allocation : allocation) : bool :=
  allocation_structure_wf allocation_count allocation &&
  allocation_layout_wf layouts allocation.

Definition allocation_id_live (memory : memory_state) (allocation_id : nat)
    : bool :=
  match nth_error memory allocation_id with
  | Some allocation => allocation_live allocation
  | None => false
  end.

Fixpoint local_allocations (locals : list local_storage) : list nat :=
  match locals with
  | [] => []
  | LocalAllocated allocation :: locals =>
      allocation :: local_allocations locals
  | _ :: locals => local_allocations locals
  end.

Fixpoint nat_mem (value : nat) (values : list nat) : bool :=
  match values with
  | [] => false
  | candidate :: values => Nat.eqb value candidate || nat_mem value values
  end.

Fixpoint nat_nodup (values : list nat) : bool :=
  match values with
  | [] => true
  | value :: values => negb (nat_mem value values) && nat_nodup values
  end.

Definition local_storage_wf (memory : memory_state)
    (storage : local_storage) : bool :=
  match storage with
  | LocalDead | LocalUnallocated => true
  | LocalAllocated allocation => allocation_id_live memory allocation
  end.

Definition exposed_allocation_wf
    (memory : memory_state) (allocation : nat) : bool :=
  Nat.ltb allocation (List.length memory).

Definition memory_addresses_fit (memory : memory_state) : bool :=
  forallb (fun a => (0 <? allocation_base a) && (allocation_end a <=? address_space_end))
    memory.

Definition prog_state_wf (layouts : layout_env) (state : prog_state) : bool :=
  let memory := state_memory state in
  memory_addresses_fit memory &&
  forallb (allocation_structure_wf (List.length memory)) memory &&
  forallb (local_storage_wf memory) (state_locals state) &&
  nat_nodup (local_allocations (state_locals state)) &&
  forallb (exposed_allocation_wf memory)
    (state_exposed_allocations state) &&
  nat_nodup (state_exposed_allocations state).

Definition commit_well_formed_state
    (layouts : layout_env) (state : prog_state) : option prog_state :=
  if prog_state_wf layouts state then Some state else None.

Definition local_state (locals : list slot) : prog_state :=
  ProgState locals [].

Definition local_address_result (state : prog_state) (local : nat)
    : access_result (value_shape * nat * nat) :=
  match nth_error (state_locals state) local with
  | Some LocalDead => AccessUb UbReadDead
  | Some LocalUnallocated => AccessUb UbReadUninitialized
  | Some (LocalAllocated allocation_id) =>
      match nth_error (state_memory state) allocation_id with
      | Some allocation =>
          if allocation_live allocation then
            AccessOk (allocation_shape allocation, allocation_id, 0%nat)
          else AccessUb UbReadDead
      | None => AccessFail
      end
  | None => AccessFail
  end.

Definition read_local_result (local : nat) (state : prog_state)
    : access_result runtime_value :=
  match local_address_result state local with
  | AccessOk (shape, allocation_id, offset) =>
      read_allocation_result (state_memory state) allocation_id offset shape
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition read_local (local : nat) (state : prog_state)
    : option runtime_value :=
  match read_local_result local state with
  | AccessOk value => Some value
  | _ => None
  end.

Definition local_read_ub_reason (state : prog_state) (local : nat)
    (reason : ub_reason) : Prop :=
  read_local_result local state = AccessUb reason.

Definition runtime_index_result (state : prog_state) (local : nat)
    : access_result nat :=
  match read_local_result local state with
  | AccessOk (VBits _ bits) => AccessOk (Z.to_nat bits)
  | AccessOk _ => AccessFail
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition runtime_index (state : prog_state) (local : nat) : option nat :=
  match runtime_index_result state local with
  | AccessOk index => Some index
  | _ => None
  end.

Fixpoint shapes_prefix_size (index : nat) (shapes : list value_shape) : nat :=
  match index, shapes with
  | O, _ => 0%nat
  | S index, shape :: shapes =>
      (shape_size shape + shapes_prefix_size index shapes)%nat
  | _, [] => 0%nat
  end.

Definition subslice_available {A : Type} (from from_end : nat)
    (values : list A) : bool :=
  Nat.leb (from + from_end) (length values).

Definition subslice_count {A : Type} (from from_end : nat)
    (values : list A) : nat :=
  Nat.sub (Nat.sub (length values) from) from_end.

Definition subslice_list {A : Type} (from from_end : nat)
    (values : list A) : list A :=
  firstn (subslice_count from from_end values) (skipn from values).

Definition replace_subslice {A : Type} (from from_end : nat)
    (values replacement : list A) : option (list A) :=
  if subslice_available from from_end values &&
     Nat.eqb (length replacement) (subslice_count from from_end values) then
    Some (firstn from values ++ replacement ++
      skipn (Nat.sub (length values) from_end) values)%list
  else None.

Definition constant_projection_index {A : Type} (offset min_length : nat)
    (from_end : bool) (values : list A) : option nat :=
  if Nat.leb min_length (length values) then
    let index := if from_end then Nat.sub (length values) offset else offset in
    if Nat.ltb index (length values) then Some index else None
  else None.

Definition source_subslice_from_end {A : Type} (from to_ : nat)
    (from_end : bool) (values : list A) : option nat :=
  if from_end then
    if subslice_available from to_ values then Some to_ else None
  else if Nat.leb from to_ && Nat.leb to_ (length values) then
    Some (Nat.sub (length values) to_)
  else None.

Definition shape_index_address (shape : value_shape) (index : nat)
    : option (value_shape * nat) :=
  match shape with
  | ShapeTuple fields =>
      match nth_error fields index with
      | Some field => Some (field, shapes_prefix_size index fields)
      | None => None
      end
  | ShapeArray element length =>
      if Nat.ltb index length then
        Some (element, (index * shape_size element)%nat)
      else None
  | _ => None
  end.

Definition shape_projection_address (shape : value_shape)
    (projection : proj_elem) : option (value_shape * nat) :=
  match projection, shape with
  | PField index _, ShapeTuple fields =>
      match nth_error fields index with
      | Some field => Some (field, shapes_prefix_size index fields)
      | None => None
      end
  | PField index _, ShapeAdt _ _ fields =>
      match nth_error fields index with
      | Some field => Some (field, (pointer_bytes + shapes_prefix_size index fields)%nat)
      | None => None
      end
  | PConstantIndex offset min_length from_end, ShapeTuple fields =>
      match constant_projection_index offset min_length from_end fields with
      | Some index => shape_index_address shape index
      | None => None
      end
  | PConstantIndex offset min_length from_end,
      ShapeArray element length =>
      match constant_projection_index offset min_length from_end
          (repeat element length) with
      | Some index => shape_index_address shape index
      | None => None
      end
  | PDowncast _ variant, ShapeAdt declaration variant' fields =>
      if Nat.eq_dec variant variant' then
        Some (ShapeAdt declaration variant fields, 0%nat)
      else None
  | PSubslice from to_ from_end, ShapeTuple fields =>
      match source_subslice_from_end from to_ from_end fields with
      | Some end_count =>
          Some (ShapeTuple (subslice_list from end_count fields),
            shapes_prefix_size from fields)
      | None => None
      end
  | PSubslice from to_ from_end, ShapeArray element length =>
      match source_subslice_from_end from to_ from_end
          (repeat element length) with
      | Some end_count =>
          let count := subslice_count from end_count (repeat element length) in
          Some (ShapeArray element count,
            (from * shape_size element)%nat)
      | None => None
      end
  | POpaqueCast _, _ | PUnwrapUnsafeBinder _, _ =>
      Some (shape, 0%nat)
  | _, _ => None
  end.

Definition layout_index_address (layouts : layout_env) (shape : value_shape)
    (index : nat) : option (value_shape * nat) :=
  match find_layout_for_shape layouts shape, shape with
  | Some layout, ShapeTuple fields =>
      match nth_error fields index with
      | Some field =>
          match layout_fields layout with
          | FieldsArray stride count =>
              if Nat.ltb index count then Some (field, (index * stride)%nat)
              else None
          | _ =>
              match layout_field_offset layout index with
              | Some offset => Some (field, offset)
              | None => None
              end
          end
      | None => None
      end
  | Some layout, ShapeArray element length =>
      if Nat.ltb index length then
        match layout_fields layout with
        | FieldsArray stride count =>
            if Nat.ltb index count then Some (element, (index * stride)%nat)
            else None
        | _ => None
        end
      else None
  | _, _ => shape_index_address shape index
  end.

Definition layout_projection_address (layouts : layout_env)
    (shape : value_shape) (projection : proj_elem)
    : option (value_shape * nat) :=
  match find_layout_for_shape layouts shape with
  | Some layout =>
      match projection, shape with
      | PField index _, ShapeTuple fields =>
          match nth_error fields index, layout_field_offset layout index with
          | Some field, Some offset => Some (field, offset)
          | _, _ => None
          end
      | PField index _, ShapeAdt _ variant fields =>
          match nth_error fields index,
              layout_variant_field_offset layout variant index with
          | Some field, Some offset => Some (field, offset)
          | _, _ =>
              match nth_error fields index, layout_field_offset layout index with
              | Some field, Some offset => Some (field, offset)
              | _, _ => None
              end
          end
      | PField index _, ShapeAdtType ty =>
          match ty, layout_variants layout with
          | TAdt _ _, VariantsSingle variant =>
              match layout_variant_field_shapes layout variant,
                  layout_variant_field_offset layout variant index with
              | Some fields, Some offset =>
                  match nth_error fields index with
                  | Some field => Some (field, offset)
                  | None => None
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      | PDowncast _ variant, ShapeAdtType ty =>
          match ty, layout_variant_field_shapes layout variant with
          | TAdt declaration _, Some fields =>
              Some (ShapeAdt declaration variant fields, 0%nat)
          | _, _ => None
          end
      | PConstantIndex offset min_length from_end, ShapeTuple fields =>
          match constant_projection_index offset min_length from_end fields with
          | Some index => layout_index_address layouts shape index
          | None => None
          end
      | PConstantIndex offset min_length from_end,
          ShapeArray element length =>
          match constant_projection_index offset min_length from_end
              (repeat element length) with
          | Some index => layout_index_address layouts shape index
          | None => None
          end
      | PSubslice from to_ from_end, ShapeTuple fields =>
          match source_subslice_from_end from to_ from_end fields with
          | Some end_count =>
              let shape' := ShapeTuple (subslice_list from end_count fields) in
              match layout_fields layout with
              | FieldsArray stride _ => Some (shape', (from * stride)%nat)
              | _ =>
                  if Nat.eqb from (List.length fields) then
                    Some (shape', layout_size layout)
                  else
                    match layout_field_offset layout from with
                    | Some offset => Some (shape', offset)
                    | None => None
                  end
              end
          | None => None
          end
      | PSubslice from to_ from_end, ShapeArray element length =>
          match source_subslice_from_end from to_ from_end
              (repeat element length) with
          | Some end_count =>
              let count :=
                subslice_count from end_count (repeat element length) in
              let shape' := ShapeArray element count in
              match layout_fields layout with
              | FieldsArray stride _ => Some (shape', (from * stride)%nat)
              | _ => None
              end
          | None => None
          end
      | _, _ => shape_projection_address shape projection
      end
  | None => shape_projection_address shape projection
  end.

Definition projection_address_result (layouts : layout_env) (state : prog_state)
    (shape : value_shape) (projection : proj_elem)
    : access_result (value_shape * nat) :=
  match projection with
  | PIndex local =>
      match runtime_index_result state local with
      | AccessOk index =>
          match layout_index_address layouts shape index with
          | Some address => AccessOk address
          | None =>
              match shape with
              | ShapeTuple _ | ShapeArray _ _ => AccessUb UbOutOfBounds
              | _ => AccessFail
              end
          end
      | AccessUb reason => AccessUb reason
      | AccessFail => AccessFail
      end
  | PDeref => AccessFail
  | _ =>
      match layout_projection_address layouts shape projection with
      | Some address => AccessOk address
      | None =>
          match projection, shape with
          | PConstantIndex _ _ _, ShapeTuple _
          | PConstantIndex _ _ _, ShapeArray _ _
          | PSubslice _ _ _, ShapeTuple _
          | PSubslice _ _ _, ShapeArray _ _ => AccessUb UbOutOfBounds
          | PDowncast _ _, ShapeAdtType _
          | PDowncast _ _, ShapeAdt _ _ _ => AccessUb UbInvalidEnumTag
          | _, _ => AccessFail
          end
      end
  end.

Fixpoint address_projections_result (layouts : layout_env) (state : prog_state)
    (shape : value_shape) (allocation offset : nat)
    (projections : list proj_elem)
    : access_result (value_shape * nat * nat) :=
  match projections with
  | [] => AccessOk (shape, allocation, offset)
  | projection :: projections =>
      match projection with
      | PDeref =>
          match read_allocation_result_with_layouts layouts
              (state_memory state) allocation offset shape with
          | AccessOk (VPointerValue pointee pointer) =>
              match resolve_pointer_allocation state pointer with
              | Some (allocation', offset') =>
                  let target_shape :=
                    match pointee, pointer_length pointer with
                    | ShapeSlice element, Some length =>
                        Some (ShapeArray element length)
                    | ShapeStr, Some length =>
                        Some (ShapeArray (ShapeBits W8) length)
                    | ShapeSlice _, None | ShapeStr, None => None
                    | _, None => Some pointee
                    | _, Some _ => None
                    end in
                  match target_shape with
                  | Some shape' =>
                      address_projections_result layouts state shape'
                        allocation' offset' projections
                  | None => AccessUb UbInvalidMetadata
                  end
              | None => AccessUb UbInvalidPointerProvenance
              end
          | AccessOk _ => AccessUb UbInvalidDeref
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
      | _ =>
          match projection_address_result layouts state shape projection with
          | AccessOk (shape', delta) =>
              address_projections_result layouts state shape' allocation
                (offset + delta) projections
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
      end
  end.

Definition address_projections (state : prog_state)
    (shape : value_shape) (allocation offset : nat)
    (projections : list proj_elem)
    : access_result (value_shape * nat * nat) :=
  address_projections_result [] state shape allocation offset projections.

Definition address_of_place_result (layouts : layout_env)
    (target : place) (state : prog_state)
    : access_result (value_shape * nat * nat) :=
  match local_address_result state (pl_local target) with
  | AccessOk (shape, allocation, offset) =>
      address_projections_result layouts state shape allocation offset
        (pl_proj target)
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition address_of_place_with_layouts (layouts : layout_env)
    (target : place) (state : prog_state)
    : option runtime_value :=
  match address_of_place_result layouts target state with
  | AccessOk (shape, allocation, offset) =>
      let slice_pointer element length :=
        Some (VPointerValue (ShapeSlice element)
          (PointerValue (ProvenanceAllocation allocation)
            (Z.of_nat offset) (PointerLength length))) in
      match rev (pl_proj target), shape with
      | PSubslice _ _ _ :: _, ShapeArray element length => slice_pointer element length
      | PDeref :: rest, ShapeArray element length =>
          match address_of_place_result layouts (Place (pl_local target) (rev rest)) state with
          | AccessOk (base_shape, base_allocation, base_offset) =>
              match read_allocation_result_with_layouts layouts (state_memory state)
                      base_allocation base_offset base_shape with
              | AccessOk (VPointerValue (ShapeSlice _) (PointerValue _ _ (PointerLength _))) =>
                  slice_pointer element length
              | _ => Some (VPointer shape allocation offset)
              end
          | _ => Some (VPointer shape allocation offset)
          end
      | _, _ => Some (VPointer shape allocation offset)
      end
  | _ => None
  end.

Definition address_of_place (target : place) (state : prog_state)
    : option runtime_value :=
  address_of_place_with_layouts [] target state.

Definition place_range_with_layouts (layouts : layout_env)
    (target : place) (state : prog_state)
    : option (value_shape * nat * nat * nat) :=
  match address_of_place_result layouts target state with
  | AccessOk (shape, allocation, offset) =>
      Some (shape, allocation, offset, shape_size_with_layouts layouts shape)
  | _ => None
  end.

Definition place_range (target : place) (state : prog_state)
    : option (value_shape * nat * nat * nat) :=
  place_range_with_layouts [] target state.

Definition denote_borrow_with_layouts (layouts : layout_env)
    (_kind : borrow_kind) (borrowed : place)
    (state : prog_state) : option (runtime_value * prog_state) :=
  match place_range_with_layouts layouts borrowed state with
  | Some (shape, allocation, offset, _) =>
      match read_allocation_result_with_layouts layouts (state_memory state)
          allocation offset shape with
      | AccessOk _ =>
          match rev (pl_proj borrowed), shape with
          | PSubslice _ _ _ :: _, ShapeArray element length =>
              Some (VPointerValue (ShapeSlice element)
                (PointerValue (ProvenanceAllocation allocation)
                  (Z.of_nat offset) (PointerLength length)), state)
          | _, _ => Some (VPointer shape allocation offset, state)
          end
      | AccessUb _ | AccessFail => None
      end
  | None => None
  end.

Definition denote_borrow (kind : borrow_kind) (borrowed : place)
    (state : prog_state) : option (runtime_value * prog_state) :=
  denote_borrow_with_layouts [] kind borrowed state.

Definition write_access_result (memory : memory_state)
    (allocation_id offset : nat) (shape : value_shape)
    : access_result unit :=
  memory_access_result (policy_may_write permissive_memory_policy)
    memory allocation_id offset (TypedOp shape).

Definition write_access_result_with_layouts (layouts : layout_env)
    (memory : memory_state) (allocation_id offset : nat) (shape : value_shape)
    : access_result unit :=
  memory_access_result_with_layouts layouts
    (policy_may_write permissive_memory_policy) memory allocation_id offset
    (TypedOp shape).

Definition allocate_local_value (local : nat) (value : runtime_value)
    (state : prog_state) : option prog_state :=
  match nth_error (state_locals state) local with
  | Some LocalUnallocated =>
      match allocate_value (state_memory state) value with
      | Some (allocation_id, memory') =>
          match set_nth local (LocalAllocated allocation_id)
              (state_locals state) with
          | Some locals => commit_well_formed_state []
              (state_with_locals_memory state locals memory')
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition allocate_local_value_with_layouts (layouts : layout_env)
    (local : nat) (value : runtime_value) (state : prog_state)
    : option prog_state :=
  match nth_error (state_locals state) local with
  | Some LocalUnallocated =>
      match allocate_value_with_layouts layouts (state_memory state) value with
      | Some (allocation_id, memory') =>
          match set_nth local (LocalAllocated allocation_id)
              (state_locals state) with
          | Some locals => commit_well_formed_state layouts
              (state_with_locals_memory state locals memory')
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition storage_live_local (local : nat) (state : prog_state)
    : option prog_state :=
  match nth_error (state_locals state) local with
  | Some (LocalAllocated allocation_id) =>
      match kill_allocation (state_memory state) allocation_id,
          set_nth local LocalUnallocated (state_locals state) with
      | Some memory', Some locals =>
          commit_well_formed_state []
            (state_with_locals_memory state locals memory')
      | _, _ => None
      end
  | Some _ =>
      match set_nth local LocalUnallocated (state_locals state) with
      | Some locals => commit_well_formed_state []
          (state_with_locals state locals)
      | None => None
      end
  | None => None
  end.

Definition storage_live_local_with_layouts
    (layouts : layout_env) (shape : value_shape)
    (local : nat) (state : prog_state) : option prog_state :=
  match nth_error (state_locals state) local with
  | None => None
  | Some storage =>
      let memory_result :=
        match storage with
        | LocalAllocated allocation =>
            kill_allocation (state_memory state) allocation
        | LocalDead | LocalUnallocated => Some (state_memory state)
        end in
      match memory_result with
      | Some memory =>
          match allocate_uninitialized_with_layouts layouts memory shape with
          | Some (allocation, memory') =>
              match set_nth local (LocalAllocated allocation)
                  (state_locals state) with
              | Some locals =>
                  commit_well_formed_state layouts
                    (state_with_locals_memory state locals memory')
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Definition storage_dead_local_with_layouts (layouts : layout_env)
    (local : nat) (state : prog_state) : option prog_state :=
  match nth_error (state_locals state) local with
  | Some (LocalAllocated allocation_id) =>
      match kill_allocation (state_memory state) allocation_id,
          set_nth local LocalDead (state_locals state) with
      | Some memory', Some locals =>
          commit_well_formed_state layouts
            (state_with_locals_memory state locals memory')
      | _, _ => None
      end
  | Some _ =>
      match set_nth local LocalDead (state_locals state) with
      | Some locals => commit_well_formed_state layouts
          (state_with_locals state locals)
      | None => None
      end
  | None => None
  end.

Definition storage_dead_local (local : nat) (state : prog_state)
    : option prog_state :=
  storage_dead_local_with_layouts [] local state.

Definition deinitialize_place_with_layouts (layouts : layout_env)
    (target : place) (state : prog_state)
    : option prog_state :=
  match address_of_place_result layouts target state with
  | AccessOk (shape, allocation, offset) =>
      match deinitialize_allocation (state_memory state) allocation offset
          (shape_size_with_layouts layouts shape) with
      | Some memory' => commit_well_formed_state layouts
          (state_with_memory state memory')
      | None => None
      end
  | AccessUb _ | AccessFail => None
  end.

Definition deinitialize_place (target : place) (state : prog_state)
    : option prog_state :=
  deinitialize_place_with_layouts [] target state.

Definition read_place_result_with_layouts (layouts : layout_env)
    (target : place) (state : prog_state)
    : access_result runtime_value :=
  match address_of_place_result layouts target state with
  | AccessOk (shape, allocation, offset) =>
      read_allocation_result_with_layouts layouts (state_memory state)
        allocation offset shape
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition read_place_result (target : place) (state : prog_state)
    : access_result runtime_value :=
  read_place_result_with_layouts [] target state.

Definition read_place_with_layouts (layouts : layout_env)
    (target : place) (state : prog_state)
    : option runtime_value :=
  match read_place_result_with_layouts layouts target state with
  | AccessOk value => Some value
  | _ => None
  end.

Definition read_place (target : place) (state : prog_state)
    : option runtime_value :=
  read_place_with_layouts [] target state.

Lemma read_local_is_direct_place_read local state :
  read_local local state = read_place (Place local []) state.
Proof.
  unfold read_local, read_local_result, read_place, read_place_with_layouts,
    read_place_result, read_place_result_with_layouts,
    address_of_place_result.
  simpl.
  destruct (local_address_result state local)
    as [[[shape allocation] offset] | reason |]; reflexivity.
Qed.

Lemma local_and_pointer_read_results_agree
    layouts local state shape allocation :
  shape_is_unsized shape = false ->
  shape_size_with_layouts layouts shape <> 0%nat ->
  local_address_result state local = AccessOk (shape, allocation, 0%nat) ->
  read_place_result_with_layouts layouts (Place local []) state =
  read_through_pointer_result layouts shape
    (PointerValue (ProvenanceAllocation allocation) 0 PointerThin) state.
Proof.
  intros Hsized Hnonzero Haddress.
  unfold read_place_result_with_layouts, address_of_place_result.
  cbn [pl_local pl_proj].
  rewrite Haddress. simpl.
  unfold read_through_pointer_result.
  rewrite Hsized.
  assert (Hsize :
      Nat.eqb (shape_size_with_layouts layouts shape) 0 = false).
  { apply Nat.eqb_neq. exact Hnonzero. }
  rewrite Hsize. reflexivity.
Qed.

Definition write_place_with_layouts (layouts : layout_env)
    (target : place) (value : runtime_value)
    (state : prog_state) : option prog_state :=
  match pl_proj target,
      nth_error (state_locals state) (pl_local target) with
  | [], Some LocalUnallocated =>
      allocate_local_value_with_layouts layouts (pl_local target) value state
  | _, _ =>
      match address_of_place_result layouts target state with
      | AccessOk (shape, allocation, offset) =>
          match write_allocation_with_layouts layouts (state_memory state)
              allocation offset shape value with
          | Some memory' => commit_well_formed_state layouts
              (state_with_memory state memory')
          | None => None
          end
      | AccessUb _ | AccessFail => None
      end
  end.

Definition write_place_result_with_layouts (layouts : layout_env)
    (target : place) (value : runtime_value)
    (state : prog_state) : access_result prog_state :=
  match pl_proj target,
      nth_error (state_locals state) (pl_local target) with
  | [], Some LocalUnallocated =>
      match allocate_local_value_with_layouts layouts (pl_local target) value state with
      | Some state' => AccessOk state'
      | None => AccessFail
      end
  | _, _ =>
      match address_of_place_result layouts target state with
      | AccessOk (shape, allocation, offset) =>
          match write_allocation_operation_result_with_layouts layouts
              (state_memory state) allocation offset (TypedOp shape)
              (OVTyped value) with
          | AccessOk memory' =>
              match commit_well_formed_state layouts
                  (state_with_memory state memory') with
              | Some state' => AccessOk state'
              | None => AccessFail
              end
          | AccessUb reason => AccessUb reason
          | AccessFail => AccessFail
          end
      | AccessUb reason => AccessUb reason
      | AccessFail => AccessFail
      end
  end.

Lemma write_place_result_agrees layouts target value state state' :
  write_place_result_with_layouts layouts target value state = AccessOk state' <->
  write_place_with_layouts layouts target value state = Some state'.
Proof.
  unfold write_place_result_with_layouts, write_place_with_layouts,
    write_allocation_with_layouts.
  destruct (pl_proj target), (nth_error (state_locals state) (pl_local target))
    as [[| |]|];
    try (destruct (allocate_local_value_with_layouts _ _ _ _);
         split; intros H; congruence);
    destruct (address_of_place_result layouts target state) as [[[? ?] ?]| |];
    try (split; intros H; discriminate);
    destruct (write_allocation_operation_result_with_layouts _ _ _ _ _ _);
    try (split; intros H; discriminate);
    destruct (commit_well_formed_state _ _); split; intros H; congruence.
Qed.

Definition place_initialized_result (layouts : layout_env)
    (target : place) (state : prog_state) : access_result bool :=
  match address_of_place_result layouts target state with
  | AccessOk (shape, allocation, offset) =>
      match nth_error (state_memory state) allocation with
      | Some a =>
          AccessOk (existsb (fun initialized => initialized)
            (firstn (shape_size_with_layouts layouts shape)
              (skipn offset (allocation_init a))))
      | None => AccessFail
      end
  | AccessUb reason => AccessUb reason
  | AccessFail => AccessFail
  end.

Definition write_place (target : place) (value : runtime_value)
    (state : prog_state) : option prog_state :=
  write_place_with_layouts [] target value state.

Definition read_place_ub_reason_with_layouts (layouts : layout_env)
    (state : prog_state) (target : place) (reason : ub_reason) : Prop :=
  read_place_result_with_layouts layouts target state = AccessUb reason.

Definition read_place_ub_reason (state : prog_state) (target : place)
    (reason : ub_reason) : Prop :=
  read_place_ub_reason_with_layouts [] state target reason.

Definition write_place_ub_reason_with_layouts (layouts : layout_env)
    (state : prog_state) (target : place) (reason : ub_reason) : Prop :=
  match pl_proj target with
  | [] => False
  | _ =>
      match address_of_place_result layouts target state with
      | AccessOk (shape, allocation, offset) =>
          write_access_result_with_layouts layouts (state_memory state)
            allocation offset shape = AccessUb reason
      | AccessUb actual => actual = reason
      | AccessFail => False
      end
  end.

Definition write_place_ub_reason (state : prog_state) (target : place)
    (reason : ub_reason) : Prop :=
  write_place_ub_reason_with_layouts [] state target reason.

Definition write_place_value_ub_reason_with_layouts (layouts : layout_env)
    (state : prog_state) (target : place) (value : runtime_value)
    (reason : ub_reason) : Prop :=
  match pl_proj target,
      nth_error (state_locals state) (pl_local target) with
  | [], Some LocalUnallocated => False
  | _, _ =>
      match address_of_place_result layouts target state with
      | AccessOk (shape, allocation, offset) =>
          write_allocation_operation_result_with_layouts layouts
            (state_memory state) allocation offset (TypedOp shape)
            (OVTyped value) = AccessUb reason
      | AccessUb actual => actual = reason
      | AccessFail => False
      end
  end.

Definition invalid_deref_in_place_with_layouts (layouts : layout_env)
    (state : prog_state) (target : place) : Prop :=
  read_place_ub_reason_with_layouts layouts state target UbInvalidDeref.

Definition invalid_deref_in_place (state : prog_state) (target : place) : Prop :=
  invalid_deref_in_place_with_layouts [] state target.

End Addresses.

Definition bump_next (m : memory_state) : Z :=
  fold_left (fun acc a => Z.max acc (allocation_end a)) m 4096.

Definition bump_base (m : memory_state) (size align : nat) : option Z :=
  match align with
  | O => None
  | S _ =>
      let a := Z.of_nat align in
      let base := ((bump_next m + a - 1) / a) * a in
      if base + Z.of_nat (Nat.max 1 size) <=? address_space_end then Some base else None
  end.

Lemma bump_fold_ge : forall m acc, acc <= fold_left (fun acc a => Z.max acc (allocation_end a)) m acc.
Proof.
  induction m as [|a m IH]; intros acc; cbn; [lia|].
  specialize (IH (Z.max acc (allocation_end a))). lia.
Qed.

Lemma bump_fold_end : forall m acc a,
  In a m -> allocation_end a <= fold_left (fun acc a => Z.max acc (allocation_end a)) m acc.
Proof.
  induction m as [|b m IH]; intros acc a Hin; [destruct Hin|].
  destruct Hin as [->|Hin]; cbn.
  - pose proof (bump_fold_ge m (Z.max acc (allocation_end a))). lia.
  - apply IH. exact Hin.
Qed.

Lemma bump_base_spec : forall m size align base,
  bump_base m size align = Some base ->
  (0 < Z.of_nat align /\ bump_next m <= base /\ Z.modulo base (Z.of_nat align) = 0 /\
   base + Z.of_nat (Nat.max 1 size) <= address_space_end).
Proof.
  intros m size align base H. unfold bump_base in H.
  destruct align as [|align']; [discriminate|].
  set (a := Z.of_nat (S align')) in *.
  destruct (_ <=? _) eqn:Hfit; [|discriminate].
  injection H as <-. apply Z.leb_le in Hfit.
  assert (Ha : 0 < a) by lia.
  split; [exact Ha|]. split.
  - pose proof (Z.div_mod (bump_next m + a - 1) a ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (bump_next m + a - 1) a Ha) as Hb.
    rewrite Z.mul_comm. lia.
  - split; [apply Z.mod_mul; lia | exact Hfit].
Qed.

Lemma bump_positive : forall m size align base,
  bump_base m size align = Some base -> 0 < base.
Proof.
  intros m size align base H. destruct (bump_base_spec m size align base H) as [_ [Hn _]].
  pose proof (bump_fold_ge m 4096). unfold bump_next in Hn. lia.
Qed.

Lemma bump_aligned : forall m size align base,
  bump_base m size align = Some base -> Z.modulo base (Z.of_nat align) = 0.
Proof. intros m size align base H. apply (bump_base_spec m size align base H). Qed.

Lemma bump_fits : forall m size align base,
  bump_base m size align = Some base ->
  base + Z.of_nat (Nat.max 1 size) <= address_space_end.
Proof. intros m size align base H. apply (bump_base_spec m size align base H). Qed.

Lemma bump_disjoint : forall m size align base a,
  bump_base m size align = Some base -> In a m -> allocation_live a = true ->
  allocation_end a <= base \/ base + Z.of_nat (Nat.max 1 size) <= allocation_base a.
Proof.
  intros m size align base a H Hin _. left.
  destruct (bump_base_spec m size align base H) as [_ [Hn _]].
  pose proof (bump_fold_end m 4096 a Hin). unfold bump_next in Hn. lia.
Qed.

Definition bump_addr : AddrAlg := {|
  choose_base := bump_base;
  choose_base_positive := bump_positive;
  choose_base_aligned := bump_aligned;
  choose_base_fits := bump_fits;
  choose_base_disjoint := bump_disjoint;
|}.

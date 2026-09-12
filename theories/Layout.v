From RustRocq Require Import Syntax.
From Stdlib Require Import Bool List String ZArith.

Import ListNotations.
Local Open Scope string_scope.

Inductive primitive_layout :=
  | PrimInt (bits : nat) (signed : bool)
  | PrimFloat (bits : nat)
  | PrimPointer (address_space bits : nat).

Record scalar_layout := ScalarLayout {
  scalar_primitive : primitive_layout;
  scalar_initialized : bool;
  scalar_valid_start : Z;
  scalar_valid_end : Z;
}.

Inductive abi_layout :=
  | AbiScalar (scalar : scalar_layout)
  | AbiScalarPair (first second : scalar_layout)
  | AbiMemory (sized : bool).

Inductive tag_encoding :=
  | TagDirect
  | TagNiche
      (untagged_variant niche_variants_start niche_variants_end : nat)
      (niche_start : Z).

Record variant_layout := VariantLayoutData {
  variant_index : nat;
  variant_size : nat;
  variant_uninhabited : bool;
  variant_field_types : list ty;
  variant_field_offsets : list nat;
  variant_abi : abi_layout;
}.

Definition VariantLayoutWithFields
    (index size : nat) (uninhabited : bool)
    (field_types : list ty) (offsets : list nat) (abi : abi_layout)
    : variant_layout :=
  VariantLayoutData index size uninhabited field_types offsets abi.

Inductive fields_layout :=
  | FieldsPrimitive
  | FieldsUnion (count : nat)
  | FieldsArray (stride count : nat)
  | FieldsArbitrary (offsets : list nat).

Inductive variants_layout :=
  | VariantsEmpty
  | VariantsSingle (index : nat)
  | VariantsMultiple
      (tag : scalar_layout)
      (tag_field : nat)
      (encoding : tag_encoding)
      (variants : list variant_layout).

Record type_layout := TypeLayoutData {
  layout_id : string;
  layout_ty : ty;
  layout_size : nat;
  layout_align : nat;
  layout_uninhabited : bool;
  layout_field_types : list ty;
  layout_fields : fields_layout;
  layout_variants : variants_layout;
  layout_abi : abi_layout;
}.

Definition TypeLayoutWithFields
    (id : string) (t : ty) (size align : nat) (uninhabited : bool)
    (field_types : list ty) (fields : fields_layout)
    (variants : variants_layout) (abi : abi_layout) : type_layout :=
  TypeLayoutData id t size align uninhabited field_types fields variants abi.

Definition layout_env := list type_layout.

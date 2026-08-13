From Stdlib Require Import Bool List String ZArith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive int_width := W8 | W16 | W32 | W64 | W128 | WPointer.
Inductive mutability := Shared | Mut.

Inductive vmir_ty :=
  | TyUnit
  | TyBool
  | TyChar
  | TyFloat (bits : nat)
  | TyInt (width : int_width)
  | TyUint (width : int_width)
  | TyNever
  | TyStr
  | TyTuple (fields : list vmir_ty)
  | TyArray (element : vmir_ty) (length : nat)
  | TySlice (element : vmir_ty)
  | TyAdt (declaration : string) (arguments : list vmir_ty)
  | TyRef (kind : mutability) (pointee : vmir_ty)
  | TyRawPtr (kind : mutability) (pointee : vmir_ty).

Definition int_width_eqb (left right : int_width) : bool :=
  match left, right with
  | W8, W8 | W16, W16 | W32, W32 | W64, W64 | W128, W128
  | WPointer, WPointer => true
  | _, _ => false
  end.

Fixpoint vmir_ty_eqb (lhs rhs : vmir_ty) : bool :=
  let fix vmir_tys_eqb (lhss rhss : list vmir_ty) : bool :=
    match lhss, rhss with
    | [], [] => true
    | lhs :: lhss, rhs :: rhss =>
        vmir_ty_eqb lhs rhs && vmir_tys_eqb lhss rhss
    | _, _ => false
    end in
  match lhs, rhs with
  | TyUnit, TyUnit | TyBool, TyBool | TyChar, TyChar
  | TyNever, TyNever | TyStr, TyStr => true
  | TyFloat left_bits, TyFloat right_bits => Nat.eqb left_bits right_bits
  | TyInt left_width, TyInt right_width
  | TyUint left_width, TyUint right_width =>
      int_width_eqb left_width right_width
  | TyTuple left_fields, TyTuple right_fields =>
      vmir_tys_eqb left_fields right_fields
  | TyArray left_element left_length, TyArray right_element right_length =>
      vmir_ty_eqb left_element right_element &&
      Nat.eqb left_length right_length
  | TySlice left_element, TySlice right_element =>
      vmir_ty_eqb left_element right_element
  | TyAdt left_decl left_args, TyAdt right_decl right_args =>
      String.eqb left_decl right_decl && vmir_tys_eqb left_args right_args
  | TyRef left_kind left_pointee, TyRef right_kind right_pointee
  | TyRawPtr left_kind left_pointee, TyRawPtr right_kind right_pointee =>
      match left_kind, right_kind with
      | Shared, Shared | Mut, Mut => vmir_ty_eqb left_pointee right_pointee
      | _, _ => false
      end
  | _, _ => false
  end.

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
  variant_field_types : list vmir_ty;
  variant_field_offsets : list nat;
  variant_abi : abi_layout;
}.

Definition VariantLayout
    (index size : nat) (uninhabited : bool)
    (offsets : list nat) (abi : abi_layout) : variant_layout :=
  VariantLayoutData index size uninhabited [] offsets abi.

Definition VariantLayoutWithFields
    (index size : nat) (uninhabited : bool)
    (field_types : list vmir_ty) (offsets : list nat) (abi : abi_layout)
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
  layout_ty : vmir_ty;
  layout_size : nat;
  layout_align : nat;
  layout_uninhabited : bool;
  layout_field_types : list vmir_ty;
  layout_fields : fields_layout;
  layout_variants : variants_layout;
  layout_abi : abi_layout;
}.

Definition TypeLayout
    (id : string) (ty : vmir_ty) (size align : nat) (uninhabited : bool)
    (fields : fields_layout) (variants : variants_layout) (abi : abi_layout)
    : type_layout :=
  TypeLayoutData id ty size align uninhabited [] fields variants abi.

Definition TypeLayoutWithFields
    (id : string) (ty : vmir_ty) (size align : nat) (uninhabited : bool)
    (field_types : list vmir_ty) (fields : fields_layout)
    (variants : variants_layout) (abi : abi_layout) : type_layout :=
  TypeLayoutData id ty size align uninhabited field_types fields variants abi.

Definition layout_env := list type_layout.

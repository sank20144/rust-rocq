From RustRocq Require Import Syntax Layout LayoutAlg Memory Subst Denote Lib.Models Lib.X86_64.
From Generated Require Import oak_bitmap_allocator.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition size_4k : ty := TAdt "x86_64::structures::paging::Size4KiB" [].

Definition inst (n : Z) : list garg := [GTy size_4k; GConst (CValue (TUint WSize) n)].

Definition oak_model : model := models [x86_64_model].

Definition P : program :=
  MkProgram adts bodies impls (first_order oak_model) (first_order_monotone oak_model).

Definition allocator_ty (n : Z) : ty :=
  TAdt "bitmap_frame_allocator::BitmapAllocator" (inst n).

Definition bit_array (words : list Z) : runtime_value :=
  VAdt "bitvec::array::BitArray" 0 [phantom; VArray (ShapeBits W64) (map (VBits W64) words)].

Definition allocator (allocated valid : list Z) (s e : Z) : runtime_value :=
  VAdt "bitmap_frame_allocator::BitmapAllocator" 0
    [bit_array allocated; bit_array valid; phys_frame_range s e].

Definition holding (n : Z) (v : runtime_value) : memory_state :=
  match allocate_typed_value_with_layouts (layout_env_of adts [allocator_ty n]) []
          (ShapeAdtType (allocator_ty n)) v with
  | Some (_, m) => m
  | None => []
  end.

Definition self_ref (n : Z) : runtime_value := VPointer (ShapeAdtType (allocator_ty n)) 0 0.

Definition frame := subst_body (inst 1) bitmap_frame_allocator_BitmapAllocator_S_N_1_frame.

Definition frame_idx :=
  subst_body (inst 1) bitmap_frame_allocator_BitmapAllocator_S_N_1_frame_idx.

Definition fresh := holding 1 (allocator [0] [0] 0 4096).

Definition some (v : runtime_value) : runtime_value := VAdt "core::option::Option" 1 [v].

Definition none : runtime_value := VAdt "core::option::Option" 0 [].

Example frame_zero_is_the_start_of_the_range :
  MeansOn P frame fresh [self_ref 1; VBits WSize 0] (ARet (some (phys_frame 0))).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Example frame_one_is_the_end_of_a_one_frame_range :
  MeansOn P frame fresh [self_ref 1; VBits WSize 1] (ARet (some (phys_frame 4096))).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Example frame_two_is_outside_a_one_frame_range :
  MeansOn P frame fresh [self_ref 1; VBits WSize 2] (ARet none).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Example frame_idx_of_the_end_frame :
  MeansOn P frame_idx fresh [self_ref 1; phys_frame 4096] (ARet (some (VBits WSize 1))).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Example frame_idx_of_a_frame_past_the_end :
  MeansOn P frame_idx fresh [self_ref 1; phys_frame 8192] (ARet none).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

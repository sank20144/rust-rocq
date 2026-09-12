From RustRocq Require Import Syntax Layout LayoutAlg Memory Subst Denote.
From RustRocq Require Import Lib.Models Lib.X86_64 Lib.Core Lib.Bitvec Lib.Iter Lib.Oak.
From Generated Require Import oak_bitmap_allocator.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition size_4k : ty := TAdt "x86_64::structures::paging::Size4KiB" [].

Definition inst (n : Z) : list garg := [GTy size_4k; GConst (CValue (TUint WSize) n)].

Definition P : program :=
  MkProgram adts bodies impls (oak_oracle true) (oak_oracle_monotone true).

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

Definition inst_body (b : body) : body := subst_body (inst 1) b.

Definition num_valid := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_num_valid.
Definition num_allocated := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_num_allocated.
Definition mark_valid := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_mark_valid.
Definition allocate := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_allocate.
Definition available := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_available.
Definition new := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_new.
Definition allocate_frame :=
  inst_body
    bitmap_frame_allocator_BitmapAllocator_S_N_1_as_x86_64_structures_paging_FrameAllocator_S_allocate_frame.
Definition deallocate_frame :=
  inst_body
    bitmap_frame_allocator_BitmapAllocator_S_N_1_as_x86_64_structures_paging_FrameDeallocator_S_deallocate_frame.

Definition after (b : body) (mem : memory_state) (args : list runtime_value) : memory_state :=
  match run_with P b mem args 1000%nat with
  | Some (Ok _ st) => state_memory st
  | _ => []
  end.

Definition self : runtime_value := self_ref 1.

Definition frame_at (k : Z) : runtime_value := phys_frame (k * 4096).

Definition frames (k l : Z) : runtime_value := phys_frame_range (k * 4096) (l * 4096).

Definition mark (mem : memory_state) (k l : Z) : memory_state :=
  after mark_valid mem [self; frames k l; VBool true].

Definition one_frame := Eval vm_compute in holding 1 (allocator [0] [0] 0 4096).

Example silly_allocator_invalid :
  MeansOn P allocate_frame one_frame [self] (ARet none).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Definition one_valid := Eval vm_compute in mark one_frame 0 1.

Example silly_allocator_valid_counts :
  MeansOn P num_valid one_valid [self] (ARet (VBits WSize 1))
  /\ MeansOn P num_allocated one_valid [self] (ARet (VBits WSize 0)).
Proof. split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Example silly_allocator_valid_allocates_frame_zero :
  MeansOn P allocate_frame one_valid [self] (ARet (some (frame_at 0))).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Definition one_taken := Eval vm_compute in after allocate_frame one_valid [self].

Example silly_allocator_valid_counts_after :
  MeansOn P num_valid one_taken [self] (ARet (VBits WSize 1))
  /\ MeansOn P num_allocated one_taken [self] (ARet (VBits WSize 1)).
Proof. split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Example double_allocate :
  MeansOn P allocate_frame one_taken [self] (ARet none).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Definition one_freed := Eval vm_compute in after deallocate_frame one_taken [self; frame_at 0].

Example realloc :
  MeansOn P deallocate_frame one_taken [self; frame_at 0] (ARet VUnit)
  /\ MeansOn P num_allocated one_freed [self] (ARet (VBits WSize 0))
  /\ MeansOn P allocate_frame one_freed [self] (ARet (some (frame_at 0))).
Proof. repeat split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Definition high := Eval vm_compute in mark (holding 1 (allocator [0] [0] 4096 8192)) 1 2.

Example alloc_hi :
  MeansOn P allocate_frame high [self] (ARet (some (frame_at 1))).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Definition holes := Eval vm_compute in mark (mark (holding 1 (allocator [0] [0] 0 12288)) 0 1) 2 3.
Definition holes1 := Eval vm_compute in after allocate_frame holes [self].
Definition holes2 := Eval vm_compute in after allocate_frame holes1 [self].

Example hole_in_validity :
  MeansOn P allocate_frame holes [self] (ARet (some (frame_at 0)))
  /\ MeansOn P allocate_frame holes1 [self] (ARet (some (frame_at 2)))
  /\ MeansOn P allocate_frame holes2 [self] (ARet none).
Proof. repeat split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Definition nine := Eval vm_compute in mark (holding 1 (allocator [0] [0] 0 (9 * 4096))) 0 9.

Example new_allocator_success_counts :
  MeansOn P num_valid nine [self] (ARet (VBits WSize 9))
  /\ MeansOn P num_allocated nine [self] (ARet (VBits WSize 0)).
Proof. split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Definition two := Eval vm_compute in mark (holding 1 (allocator [0] [0] 0 8192)) 0 2.
Definition two1 := Eval vm_compute in after allocate two [self; frames 0 1].
Definition two2 := Eval vm_compute in after allocate_frame two1 [self].

Example test_allocate_specific_region :
  MeansOn P allocate two [self; frames 0 1] (ARet (some (frames 0 1)))
  /\ MeansOn P allocate two1 [self; frames 0 1] (ARet none)
  /\ MeansOn P allocate two1 [self; frames 0 2] (ARet none)
  /\ MeansOn P allocate_frame two1 [self] (ARet (some (frame_at 1)))
  /\ MeansOn P allocate two2 [self; frames 0 2] (ARet none)
  /\ MeansOn P allocate two2 [self; frames 1 2] (ARet none)
  /\ MeansOn P allocate_frame two2 [self] (ARet none).
Proof. repeat split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Example new_zeroes_both_arrays :
  MeansOn P new [] [frames 0 1] (ARet (allocator [0] [0] 0 4096)).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Example available_is_valid_and_not_allocated :
  MeansOn P available one_valid [self] (ARet (bit_array [1])).
Proof. apply (means_on_within P 100). vm_compute. reflexivity. Qed.

Definition largest_available := inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_largest_available.
Definition allocate_contiguous :=
  inst_body bitmap_frame_allocator_BitmapAllocator_S_N_1_allocate_contiguous.

Definition four := Eval vm_compute in mark (holding 1 (allocator [0] [0] 0 16384)) 0 4.
Definition four_hole := Eval vm_compute in after mark_valid four [self; frames 1 2; VBool false].

Example get_largest :
  MeansOn P largest_available four [self] (ARet (some (frames 0 4)))
  /\ MeansOn P largest_available four_hole [self] (ARet (some (frames 2 4))).
Proof. split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

Definition three_valid := Eval vm_compute in mark (holding 1 (allocator [0] [0] 0 12288)) 0 3.
Definition contiguous2 := Eval vm_compute in after allocate_contiguous three_valid [self; VBits WSize 2].
Definition contiguous1 := Eval vm_compute in after allocate_contiguous contiguous2 [self; VBits WSize 1].

Example test_allocate_contiguous :
  MeansOn P allocate_contiguous three_valid [self; VBits WSize 4] (ARet none)
  /\ MeansOn P allocate_contiguous three_valid [self; VBits WSize 2] (ARet (some (frames 0 2)))
  /\ MeansOn P allocate_contiguous contiguous2 [self; VBits WSize 1] (ARet (some (frames 2 3)))
  /\ MeansOn P allocate_contiguous contiguous1 [self; VBits WSize 2] (ARet none)
  /\ MeansOn P allocate_frame contiguous1 [self] (ARet none).
Proof. repeat split; apply (means_on_within P 100); vm_compute; reflexivity. Qed.

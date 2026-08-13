From Stdlib Require Import List String ZArith.

Import ListNotations.
Open Scope string_scope.

Definition rs_def_id := string.
Definition rs_symbol := string.
Definition rs_local_id := nat.
Definition rs_block_id := nat.
Definition rs_scope_id := nat.
Definition rs_type_id := nat.
Definition rs_type_const_id := nat.
Definition rs_region_id := nat.
Definition rs_allocation_id := nat.
Definition rs_user_type_id := nat.
Definition rs_error_id := nat.

Record rs_span := RsSpan {
  rs_span_file : string;
  rs_span_start : nat;
  rs_span_end : nat;
}.

Record rs_source_info := RsSourceInfo {
  rs_source_span : rs_span;
  rs_source_scope : rs_scope_id;
}.

Inductive rs_mutability := RsNotMutable | RsMutable.
Inductive rs_safety := RsSafe | RsUnsafe.

Inductive rs_int_ty :=
  | RsI8 | RsI16 | RsI32 | RsI64 | RsI128 | RsIsize.

Inductive rs_uint_ty :=
  | RsU8 | RsU16 | RsU32 | RsU64 | RsU128 | RsUsize.

Inductive rs_float_ty := RsF16 | RsF32 | RsF64 | RsF128.

Inductive rs_generic_arg :=
  | RsArgLifetime (region : rs_region_id)
  | RsArgType (ty : rs_type_id)
  | RsArgConst (constant : rs_type_const_id).

Definition rs_generic_args := list rs_generic_arg.

Inductive rs_bound_variable_kind :=
  | RsBoundRegion (name : option rs_symbol)
  | RsBoundType (name : option rs_symbol)
  | RsBoundConst.

Inductive rs_region_kind :=
  | RsRegionEarlyParam (index : nat) (name : rs_symbol)
  | RsRegionBound
      (debruijn index : nat)
      (name : option rs_symbol)
  | RsRegionLateParam (scope : rs_def_id) (index : nat)
  | RsRegionStatic
  | RsRegionVariable (index : nat)
  | RsRegionPlaceholder
      (universe index : nat)
      (name : option rs_symbol)
  | RsRegionErased
  | RsRegionError (guarantee : rs_error_id).

Record rs_region_entry := RsRegionEntry {
  rs_region_entry_id : rs_region_id;
  rs_region_entry_kind : rs_region_kind;
}.

Record rs_fn_signature := RsFnSignature {
  rs_fn_bound_variables : list rs_bound_variable_kind;
  rs_fn_inputs : list rs_type_id;
  rs_fn_output : rs_type_id;
  rs_fn_c_variadic : bool;
  rs_fn_safety : rs_safety;
  rs_fn_abi : string;
}.

Inductive rs_alias_kind :=
  | RsAliasProjection
  | RsAliasInherent
  | RsAliasOpaque
  | RsAliasFree.

Inductive rs_integer_pattern :=
  | RsPatternRange
      (lower upper : option Z)
      (upper_inclusive : bool).

Inductive rs_existential_predicate :=
  | RsExistentialTrait (definition : rs_def_id) (args : rs_generic_args)
  | RsExistentialProjection
      (definition : rs_def_id)
      (args : rs_generic_args)
      (term_type : option rs_type_id)
      (term_const : option rs_type_const_id)
  | RsExistentialAutoTrait (definition : rs_def_id).

Inductive rs_infer_kind :=
  | RsInferType
  | RsInferInt
  | RsInferFloat
  | RsInferFreshType
  | RsInferFreshInt
  | RsInferFreshFloat.

Inductive rs_ty_kind :=
  | RsTyBool
  | RsTyChar
  | RsTyInt (kind : rs_int_ty)
  | RsTyUint (kind : rs_uint_ty)
  | RsTyFloat (kind : rs_float_ty)
  | RsTyAdt (definition : rs_def_id) (args : rs_generic_args)
  | RsTyForeign (definition : rs_def_id)
  | RsTyStr
  | RsTyArray (element : rs_type_id) (length : rs_type_const_id)
  | RsTyPat (base : rs_type_id) (pattern : rs_integer_pattern)
  | RsTySlice (element : rs_type_id)
  | RsTyRawPtr (pointee : rs_type_id) (kind : rs_mutability)
  | RsTyRef
      (region : rs_region_id)
      (pointee : rs_type_id)
      (kind : rs_mutability)
  | RsTyFnDef (definition : rs_def_id) (args : rs_generic_args)
  | RsTyFnPtr (signature : rs_fn_signature)
  | RsTyUnsafeBinder
      (bound_variables : list rs_bound_variable_kind)
      (inner : rs_type_id)
  | RsTyDynamic
      (predicates : list rs_existential_predicate)
      (region : rs_region_id)
  | RsTyClosure (definition : rs_def_id) (args : rs_generic_args)
  | RsTyCoroutineClosure (definition : rs_def_id) (args : rs_generic_args)
  | RsTyCoroutine (definition : rs_def_id) (args : rs_generic_args)
  | RsTyCoroutineWitness (definition : rs_def_id) (args : rs_generic_args)
  | RsTyNever
  | RsTyTuple (fields : list rs_type_id)
  | RsTyAlias
      (kind : rs_alias_kind)
      (definition : rs_def_id)
      (args : rs_generic_args)
  | RsTyParam (index : nat) (name : rs_symbol)
  | RsTyBound
      (debruijn : nat)
      (index : nat)
      (name : option rs_symbol)
  | RsTyPlaceholder
      (universe : nat)
      (index : nat)
      (name : option rs_symbol)
  | RsTyInfer (kind : rs_infer_kind) (index : nat)
  | RsTyError (guarantee : rs_error_id).

Record rs_type_entry := RsTypeEntry {
  rs_type_entry_id : rs_type_id;
  rs_type_entry_kind : rs_ty_kind;
}.

Inductive rs_type_const_expr :=
  | RsTypeConstParam (index : nat) (name : rs_symbol)
  | RsTypeConstValueBits (bits : Z) (size_bytes : nat)
  | RsTypeConstUnevaluated (definition : rs_def_id) (args : rs_generic_args)
  | RsTypeConstBound (debruijn index : nat)
  | RsTypeConstPlaceholder (universe index : nat)
  | RsTypeConstInfer (index : nat)
  | RsTypeConstExprNode
      (operator : string)
      (arguments : list rs_type_const_id)
  | RsTypeConstError (guarantee : rs_error_id).

Record rs_type_const_entry := RsTypeConstEntry {
  rs_type_const_entry_id : rs_type_const_id;
  rs_type_const_entry_ty : rs_type_id;
  rs_type_const_entry_expr : rs_type_const_expr;
}.

Record rs_user_type_entry := RsUserTypeEntry {
  rs_user_type_entry_id : rs_user_type_id;
  rs_user_type_entry_ty : rs_type_id;
  rs_user_type_entry_span : rs_span;
}.

Inductive rs_scalar :=
  | RsScalarInt (bits : Z) (size_bytes : nat)
  | RsScalarPointer (allocation : rs_allocation_id) (offset_bytes : nat).

Inductive rs_const_value :=
  | RsConstValueScalar (value : rs_scalar)
  | RsConstValueZeroSized
  | RsConstValueSlice (allocation : rs_allocation_id) (metadata : nat)
  | RsConstValueIndirect
      (allocation : rs_allocation_id)
      (offset_bytes : nat).

Record rs_unevaluated_const := RsUnevaluatedConst {
  rs_unevaluated_definition : rs_def_id;
  rs_unevaluated_args : rs_generic_args;
  rs_unevaluated_promoted : option nat;
}.

Record rs_allocation_relocation := RsAllocationRelocation {
  rs_relocation_offset_bytes : nat;
  rs_relocation_target : rs_allocation_id;
  rs_relocation_target_offset_bytes : nat;
}.

Record rs_memory_allocation := RsMemoryAllocation {
  rs_memory_bytes : list Z;
  rs_memory_initialized : list bool;
  rs_memory_relocations : list rs_allocation_relocation;
  rs_memory_alignment : nat;
  rs_memory_mutable : bool;
}.

Inductive rs_global_allocation_kind :=
  | RsAllocationFunction (definition : rs_def_id) (args : rs_generic_args)
  | RsAllocationVTable
      (concrete_ty : rs_type_id)
      (predicates : list rs_existential_predicate)
  | RsAllocationStatic (definition : rs_def_id)
  | RsAllocationMemory (memory : rs_memory_allocation)
  | RsAllocationTypeId (ty : rs_type_id).

Record rs_allocation_entry := RsAllocationEntry {
  rs_allocation_entry_id : rs_allocation_id;
  rs_allocation_entry_kind : rs_global_allocation_kind;
}.

Inductive rs_mir_const :=
  | RsMirConstTy (ty : rs_type_id) (constant : rs_type_const_id)
  | RsMirConstUnevaluated
      (constant : rs_unevaluated_const)
      (ty : rs_type_id)
  | RsMirConstVal (value : rs_const_value) (ty : rs_type_id).

Record rs_const_operand := RsConstOperand {
  rs_const_operand_span : rs_span;
  rs_const_operand_user_ty : option rs_user_type_id;
  rs_const_operand_const : rs_mir_const;
}.

Inductive rs_projection_elem :=
  | RsProjDeref
  | RsProjField (field : nat) (ty : rs_type_id)
  | RsProjIndex (local : rs_local_id)
  | RsProjConstantIndex
      (offset min_length : nat)
      (from_end : bool)
  | RsProjSubslice (from to_ : nat) (from_end : bool)
  | RsProjDowncast (name : option rs_symbol) (variant : nat)
  | RsProjOpaqueCast (ty : rs_type_id)
  | RsProjUnwrapUnsafeBinder (ty : rs_type_id).

Record rs_place := RsPlace {
  rs_place_local : rs_local_id;
  rs_place_projection : list rs_projection_elem;
}.

Inductive rs_runtime_checks :=
  | RsRuntimeUbChecks
  | RsRuntimeContractChecks
  | RsRuntimeOverflowChecks.

Inductive rs_operand :=
  | RsOperandCopy (source : rs_place)
  | RsOperandMove (source : rs_place)
  | RsOperandConstant (constant : rs_const_operand)
  | RsOperandRuntimeChecks (checks : rs_runtime_checks).

Inductive rs_with_retag := RsRetagYes | RsRetagNo.
Inductive rs_fake_borrow_kind := RsFakeShallow | RsFakeDeep.
Inductive rs_mut_borrow_kind :=
  | RsMutDefault
  | RsMutTwoPhaseBorrow
  | RsMutClosureCapture.

Inductive rs_borrow_kind :=
  | RsBorrowShared
  | RsBorrowFake (kind : rs_fake_borrow_kind)
  | RsBorrowMut (kind : rs_mut_borrow_kind).

Inductive rs_raw_ptr_kind :=
  | RsRawMut
  | RsRawConst
  | RsRawFakeForPtrMetadata.

Inductive rs_pointer_coercion :=
  | RsCoerceReifyFnPointer (safety : rs_safety)
  | RsCoerceUnsafeFnPointer
  | RsCoerceClosureFnPointer (safety : rs_safety)
  | RsCoerceMutToConstPointer
  | RsCoerceArrayToPointer
  | RsCoerceUnsize.

Inductive rs_coercion_source := RsCoercionAsCast | RsCoercionImplicit.

Inductive rs_cast_kind :=
  | RsCastPointerExposeProvenance
  | RsCastPointerWithExposedProvenance
  | RsCastPointerCoercion
      (coercion : rs_pointer_coercion)
      (source : rs_coercion_source)
  | RsCastIntToInt
  | RsCastFloatToInt
  | RsCastFloatToFloat
  | RsCastIntToFloat
  | RsCastPtrToPtr
  | RsCastFnPtrToPtr
  | RsCastTransmute
  | RsCastSubtype.

Inductive rs_unop := RsUnNot | RsUnNeg | RsUnPtrMetadata.

Inductive rs_binop :=
  | RsBinAdd
  | RsBinAddUnchecked
  | RsBinAddWithOverflow
  | RsBinSub
  | RsBinSubUnchecked
  | RsBinSubWithOverflow
  | RsBinMul
  | RsBinMulUnchecked
  | RsBinMulWithOverflow
  | RsBinDiv
  | RsBinRem
  | RsBinBitXor
  | RsBinBitAnd
  | RsBinBitOr
  | RsBinShl
  | RsBinShlUnchecked
  | RsBinShr
  | RsBinShrUnchecked
  | RsBinEq
  | RsBinLt
  | RsBinLe
  | RsBinNe
  | RsBinGe
  | RsBinGt
  | RsBinCmp
  | RsBinOffset.

Inductive rs_aggregate_kind :=
  | RsAggregateArray (element : rs_type_id)
  | RsAggregateTuple
  | RsAggregateAdt
      (definition : rs_def_id)
      (variant : nat)
      (args : rs_generic_args)
      (user_ty : option rs_user_type_id)
      (active_union_field : option nat)
  | RsAggregateClosure (definition : rs_def_id) (args : rs_generic_args)
  | RsAggregateCoroutine (definition : rs_def_id) (args : rs_generic_args)
  | RsAggregateCoroutineClosure
      (definition : rs_def_id)
      (args : rs_generic_args)
  | RsAggregateRawPtr (pointee : rs_type_id) (kind : rs_mutability).

Inductive rs_rvalue :=
  | RsRvalueUse (value : rs_operand) (retag : rs_with_retag)
  | RsRvalueRepeat (value : rs_operand) (count : rs_type_const_id)
  | RsRvalueRef
      (region : rs_region_id)
      (kind : rs_borrow_kind)
      (borrowed : rs_place)
  | RsRvalueThreadLocalRef (definition : rs_def_id)
  | RsRvalueRawPtr (kind : rs_raw_ptr_kind) (addressed : rs_place)
  | RsRvalueCast
      (kind : rs_cast_kind)
      (value : rs_operand)
      (target_ty : rs_type_id)
  | RsRvalueBinaryOp (op : rs_binop) (left right : rs_operand)
  | RsRvalueUnaryOp (op : rs_unop) (value : rs_operand)
  | RsRvalueDiscriminant (source : rs_place)
  | RsRvalueAggregate
      (kind : rs_aggregate_kind)
      (fields : list rs_operand)
  | RsRvalueCopyForDeref (source : rs_place)
  | RsRvalueWrapUnsafeBinder (value : rs_operand) (ty : rs_type_id)
  | RsRvalueReborrow
      (ty : rs_type_id)
      (kind : rs_mutability)
      (source : rs_place).

Inductive rs_fake_read_cause :=
  | RsFakeReadForMatchGuard
  | RsFakeReadForMatchedPlace (closure : option rs_def_id)
  | RsFakeReadForGuardBinding
  | RsFakeReadForLet (closure : option rs_def_id)
  | RsFakeReadForIndex.

Inductive rs_variance :=
  | RsCovariant | RsInvariant | RsContravariant | RsBivariant.

Inductive rs_user_projection_elem :=
  | RsUserProjDeref
  | RsUserProjField (field : nat)
  | RsUserProjIndex
  | RsUserProjConstantIndex
      (offset min_length : nat)
      (from_end : bool)
  | RsUserProjSubslice (from to_ : nat) (from_end : bool)
  | RsUserProjDowncast (name : option rs_symbol) (variant : nat)
  | RsUserProjOpaqueCast
  | RsUserProjUnwrapUnsafeBinder.

Record rs_user_type_projection := RsUserTypeProjection {
  rs_user_projection_base : rs_user_type_id;
  rs_user_projection_path : list rs_user_projection_elem;
}.

Inductive rs_coverage_kind :=
  | RsCoverageSpanMarker
  | RsCoverageBlockMarker (id : nat)
  | RsCoverageVirtualCounter (basic_coverage_block : nat).

Record rs_copy_nonoverlapping := RsCopyNonOverlapping {
  rs_copy_source : rs_operand;
  rs_copy_destination : rs_operand;
  rs_copy_count : rs_operand;
}.

Inductive rs_non_diverging_intrinsic :=
  | RsIntrinsicAssume (condition : rs_operand)
  | RsIntrinsicCopyNonOverlapping (copy : rs_copy_nonoverlapping).

Inductive rs_backward_incompatible_drop_reason := RsDropReasonEdition2024.

Inductive rs_statement_kind :=
  | RsStatementAssign (destination : rs_place) (value : rs_rvalue)
  | RsStatementFakeRead (cause : rs_fake_read_cause) (source : rs_place)
  | RsStatementSetDiscriminant (destination : rs_place) (variant : nat)
  | RsStatementStorageLive (local : rs_local_id)
  | RsStatementStorageDead (local : rs_local_id)
  | RsStatementPlaceMention (mentioned : rs_place)
  | RsStatementAscribeUserType
      (place : rs_place)
      (projection : rs_user_type_projection)
      (variance : rs_variance)
  | RsStatementCoverage (coverage : rs_coverage_kind)
  | RsStatementIntrinsic (intrinsic : rs_non_diverging_intrinsic)
  | RsStatementConstEvalCounter
  | RsStatementNop
  | RsStatementBackwardIncompatibleDropHint
      (place : rs_place)
      (reason : rs_backward_incompatible_drop_reason).

Record rs_statement := RsStatement {
  rs_statement_source_info : rs_source_info;
  rs_statement_kind_data : rs_statement_kind;
}.

Inductive rs_unwind_terminate_reason :=
  | RsUnwindReasonAbi
  | RsUnwindReasonInCleanup.

Inductive rs_unwind_action :=
  | RsUnwindContinue
  | RsUnwindUnreachable
  | RsUnwindTerminate (reason : rs_unwind_terminate_reason)
  | RsUnwindCleanup (target : rs_block_id).

Inductive rs_call_source :=
  | RsCallOverloadedOperator
  | RsCallMatchCmp
  | RsCallMisc
  | RsCallUse
  | RsCallNormal.

Inductive rs_coroutine_kind :=
  | RsCoroutineDesugared
      (desugaring source : string)
  | RsCoroutineExplicit (movability : string).

Inductive rs_assert_kind :=
  | RsAssertBoundsCheck (length index : rs_operand)
  | RsAssertOverflow (op : rs_binop) (left right : rs_operand)
  | RsAssertOverflowNeg (value : rs_operand)
  | RsAssertDivisionByZero (value : rs_operand)
  | RsAssertRemainderByZero (value : rs_operand)
  | RsAssertResumedAfterReturn (kind : rs_coroutine_kind)
  | RsAssertResumedAfterPanic (kind : rs_coroutine_kind)
  | RsAssertResumedAfterDrop (kind : rs_coroutine_kind)
  | RsAssertMisalignedPointerDereference
      (required found : rs_operand)
  | RsAssertNullPointerDereference
  | RsAssertInvalidEnumConstruction (value : rs_operand).

Record rs_spanned_operand := RsSpannedOperand {
  rs_spanned_operand_value : rs_operand;
  rs_spanned_operand_span : rs_span;
}.

Inductive rs_inline_asm_macro := RsInlineAsm | RsInlineNakedAsm.

Inductive rs_inline_asm_register :=
  | RsInlineAsmReg (name : rs_symbol)
  | RsInlineAsmRegClass (name : rs_symbol).

Inductive rs_inline_asm_template_piece :=
  | RsInlineAsmTemplateString (text : string)
  | RsInlineAsmTemplatePlaceholder
      (operand_index : nat)
      (modifier : option nat)
      (span : rs_span).

Record rs_inline_asm_options := RsInlineAsmOptions {
  rs_asm_pure : bool;
  rs_asm_nomem : bool;
  rs_asm_readonly : bool;
  rs_asm_preserves_flags : bool;
  rs_asm_noreturn : bool;
  rs_asm_nostack : bool;
  rs_asm_att_syntax : bool;
  rs_asm_raw : bool;
  rs_asm_may_unwind : bool;
}.

Inductive rs_inline_asm_operand :=
  | RsInlineAsmIn
      (register : rs_inline_asm_register)
      (value : rs_operand)
  | RsInlineAsmOut
      (register : rs_inline_asm_register)
      (late : bool)
      (place : option rs_place)
  | RsInlineAsmInOut
      (register : rs_inline_asm_register)
      (late : bool)
      (input : rs_operand)
      (output : option rs_place)
  | RsInlineAsmConst (value : rs_const_operand)
  | RsInlineAsmSymFn (value : rs_const_operand)
  | RsInlineAsmSymStatic (definition : rs_def_id)
  | RsInlineAsmLabel (target_index : nat).

Record rs_switch_targets := RsSwitchTargets {
  rs_switch_values_and_targets : list (prod Z rs_block_id);
  rs_switch_otherwise : rs_block_id;
}.

Inductive rs_terminator_kind :=
  | RsTerminatorGoto (target : rs_block_id)
  | RsTerminatorSwitchInt
      (discriminant : rs_operand)
      (targets : rs_switch_targets)
  | RsTerminatorUnwindResume
  | RsTerminatorUnwindTerminate (reason : rs_unwind_terminate_reason)
  | RsTerminatorReturn
  | RsTerminatorUnreachable
  | RsTerminatorDrop
      (place : rs_place)
      (target : rs_block_id)
      (unwind : rs_unwind_action)
      (replace : bool)
      (drop : option rs_block_id)
  | RsTerminatorCall
      (function : rs_operand)
      (arguments : list rs_spanned_operand)
      (destination : rs_place)
      (target : option rs_block_id)
      (unwind : rs_unwind_action)
      (source : rs_call_source)
      (function_span : rs_span)
  | RsTerminatorTailCall
      (function : rs_operand)
      (arguments : list rs_spanned_operand)
      (function_span : rs_span)
  | RsTerminatorAssert
      (condition : rs_operand)
      (expected : bool)
      (message : rs_assert_kind)
      (target : rs_block_id)
      (unwind : rs_unwind_action)
  | RsTerminatorYield
      (value : rs_operand)
      (resume : rs_block_id)
      (resume_argument : rs_place)
      (drop : option rs_block_id)
  | RsTerminatorCoroutineDrop
  | RsTerminatorFalseEdge
      (real_target imaginary_target : rs_block_id)
  | RsTerminatorFalseUnwind
      (real_target : rs_block_id)
      (unwind : rs_unwind_action)
  | RsTerminatorInlineAsm
      (macro : rs_inline_asm_macro)
      (template : list rs_inline_asm_template_piece)
      (operands : list rs_inline_asm_operand)
      (options : rs_inline_asm_options)
      (line_spans : list rs_span)
      (targets : list rs_block_id)
      (unwind : rs_unwind_action).

Record rs_terminator := RsTerminator {
  rs_terminator_source_info : rs_source_info;
  rs_terminator_kind_data : rs_terminator_kind;
}.

Record rs_local_decl := RsLocalDecl {
  rs_local_mutability : rs_mutability;
  rs_local_ty : rs_type_id;
  rs_local_user_types : list rs_user_type_projection;
  rs_local_source_info : rs_source_info;
}.

Record rs_basic_block := RsBasicBlock {
  rs_block_statements : list rs_statement;
  rs_block_terminator : rs_terminator;
  rs_block_is_cleanup : bool;
}.

Inductive rs_mir_phase :=
  | RsMirBuilt
  | RsMirAnalysisInitial
  | RsMirAnalysisPostCleanup
  | RsMirRuntimeInitial
  | RsMirRuntimePostCleanup
  | RsMirRuntimeOptimized.

Record rs_source_scope_data := RsSourceScopeData {
  rs_scope_data_span : rs_span;
  rs_scope_data_parent : option rs_scope_id;
  rs_scope_data_inlined_definition : option rs_def_id;
  rs_scope_data_inlined_callsite : option rs_span;
}.

Record rs_body := RsBody {
  rs_body_definition : rs_def_id;
  rs_body_phase : rs_mir_phase;
  rs_body_pass_count : nat;
  rs_body_span : rs_span;
  rs_body_argument_count : nat;
  rs_body_spread_argument : option rs_local_id;
  rs_body_locals : list rs_local_decl;
  rs_body_blocks : list rs_basic_block;
  rs_body_scopes : list rs_source_scope_data;
  rs_body_regions : list rs_region_entry;
  rs_body_types : list rs_type_entry;
  rs_body_type_constants : list rs_type_const_entry;
  rs_body_user_types : list rs_user_type_entry;
  rs_body_allocations : list rs_allocation_entry;
  rs_body_required_constants : option (list rs_const_operand);
  rs_body_is_polymorphic : bool;
  rs_body_injection_phase : option rs_mir_phase;
  rs_body_tainted_by_errors : option rs_error_id;
}.

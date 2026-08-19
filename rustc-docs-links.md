# rustc_middle::mir

| type | url |
|---|---|
| `Body` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Body.html |
| `BasicBlockData` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.BasicBlockData.html |
| `LocalDecl` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.LocalDecl.html |
| `Statement` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Statement.html |
| `StatementKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html |
| `Terminator` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Terminator.html |
| `TerminatorKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html |
| `Rvalue` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Rvalue.html |
| `Operand` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Operand.html |
| `Place` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Place.html |
| `ProjectionElem` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.ProjectionElem.html |
| `Const` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Const.html |
| `ConstOperand` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.ConstOperand.html |
| `ConstValue` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.ConstValue.html |
| `interpret::Scalar` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/interpret/enum.Scalar.html |
| `AggregateKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.AggregateKind.html |
| `BorrowKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.BorrowKind.html |
| `FakeBorrowKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.FakeBorrowKind.html |
| `MutBorrowKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.MutBorrowKind.html |
| `CastKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.CastKind.html |
| `CoercionSource` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.CoercionSource.html |
| `BinOp` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.BinOp.html |
| `UnOp` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.UnOp.html |
| `AssertKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.AssertKind.html |
| `UnwindAction` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.UnwindAction.html |
| `UnwindTerminateReason` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.UnwindTerminateReason.html |
| `InlineAsmOperand` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.InlineAsmOperand.html |
| `InlineAsmMacro` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.InlineAsmMacro.html |
| `FakeReadCause` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.FakeReadCause.html |
| `NonDivergingIntrinsic` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.NonDivergingIntrinsic.html |
| `CallSource` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.CallSource.html |
| `RuntimeChecks` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.RuntimeChecks.html |
| `RawPtrKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.RawPtrKind.html |
| `WithRetag` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.WithRetag.html |
| `Mutability` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.Mutability.html |

# Types

| type | url |
|---|---|
| `TyKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.TyKind.html |
| `ConstKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.ConstKind.html |
| `RegionKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.RegionKind.html |
| `ClauseKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.ClauseKind.html |
| `GenericArgKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.GenericArgKind.html |
| `ExistentialPredicate` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.ExistentialPredicate.html |
| `PatternKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.PatternKind.html |
| `BoundVarIndexKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.BoundVarIndexKind.html |
| `Variance` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_type_ir/enum.Variance.html |
| `ty::GenericParamDefKind` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/enum.GenericParamDefKind.html |
| `ty::adjustment::PointerCoercion` | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/adjustment/enum.PointerCoercion.html |
| `ty::TyKind` alias | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/type.TyKind.html |
| `ty::ClauseKind` alias | https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/type.ClauseKind.html |

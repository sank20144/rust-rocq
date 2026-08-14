From RustRocq Require Import Syntax Subst.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition no_facts : facts :=
  Facts [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [].

Definition id_body (t : ty) (generics : list generic_param) : body := Body
       "id"
       "t.rs"
       NoSpan
   generics
     [BdWellFormedTy t]
       1
     [ LocalDecl t Mut None NoSpan
                 ; LocalDecl t Imm (Some "x") NoSpan
                 ]
     [ BasicBlock 0
                     [Stmt NoSpan (SAssign (Place 0 [])
                        (RUse (OCopy (Place 1 [])) RetagNo))]
                     (Term NoSpan TReturn)
                     false
                 ]
    []
   no_facts.

Definition id_generic : body := id_body (TParam 0 "T") [GpTy 0 "T"].

Example instantiate_at_u32 :
  subst_body [GTy (TUint W32)] id_generic = id_body (TUint W32) [].
Proof. reflexivity. Qed.

Example instantiate_at_a_reference :
  subst_body [GTy (TRef RStatic TStr Imm)] id_generic
  = id_body (TRef RStatic TStr Imm) [].
Proof. reflexivity. Qed.

Example substituting_no_arguments_is_the_identity :
  subst_body [] id_generic = id_generic.
Proof. reflexivity. Qed.

Example monomorphic_bodies_are_untouched :
  subst_body [GTy (TUint W32)] (id_body TBool []) = id_body TBool [].
Proof. reflexivity. Qed.

Example wrong_argument_kind_is_reported :
  subst_body [GLifetime RStatic] id_generic
  = id_body (TError "generic argument kind mismatch") [].
Proof. reflexivity. Qed.

Example substitution_reaches_under_constructors :
  subst_ty [GTy (TInt W8)]
    (TTuple [TSlice (TParam 0 "T"); TAdt "Vec" [GTy (TParam 0 "T")]])
  = TTuple [TSlice (TInt W8); TAdt "Vec" [GTy (TInt W8)]].
Proof. reflexivity. Qed.

Example all_three_parameter_kinds_share_an_index_space :
  subst_ty [GLifetime RStatic; GTy TBool; GConst (CValue (TUint WSize) 4%Z)]
    (TRef (RParam 0 "'a") (TArray (TParam 1 "T") (CParam 2 "N")) Imm)
  = TRef RStatic (TArray TBool (CValue (TUint WSize) 4%Z)) Imm.
Proof. reflexivity. Qed.

From RustRocq Require Import Syntax.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Definition sp := Span 1 0 3 1.

Definition l (n : nat) : place := Place n [].

Definition add_body : body := Body
        "add"
        "tests/inputs/simple.rs"
        sp
    []
      []
   2
      [ LocalDecl (TInt W32) Mut None sp
                  ; LocalDecl (TInt W32) Imm (Some "a") sp
                  ; LocalDecl (TInt W32) Imm (Some "b") sp
                  ; LocalDecl (TTuple [TInt W32; TBool]) Mut None sp
                  ]
  [ BasicBlock 0
      [ Stmt sp (SAssign (l 3)
          (RBinaryOp BAddWithOverflow (OCopy (l 1)) (OCopy (l 2)))) ]
      (Term sp (TAssert
        (OMove (Place 3 [PField 1 TBool]))
        false
        (AsOverflow BAdd (OCopy (l 1)) (OCopy (l 2)))
        1
        UaContinue))
      false
  ; BasicBlock 1
      [ Stmt sp (SAssign (l 0)
          (RUse (OMove (Place 3 [PField 0 (TInt W32)])) RetagNo)) ]
      (Term sp TReturn)
      false
  ]
   []
     (Facts [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []).

Example add_has_two_blocks : length (bd_blocks add_body) = 2.
Proof. reflexivity. Qed.

Example add_returns_from_last_block :
  option_map (fun b => tm_kind (bb_term b)) (nth_error (bd_blocks add_body) 1)
  = Some TReturn.
Proof. reflexivity. Qed.

Example add_takes_two_args : bd_arg_count add_body = 2.
Proof. reflexivity. Qed.

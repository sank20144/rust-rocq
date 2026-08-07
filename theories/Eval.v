From RustRocq Require Import Syntax.
From Stdlib Require Import String List ZArith Arith.
Import ListNotations.

Local Open Scope string_scope.

Inductive value :=
  | VInt (z : Z)
  | VBool (b : bool)
  | VUnit
  | VTuple (vs : list value).

Definition locals := nat -> option value.

Definition set (l : locals) (n : nat) (v : value) : locals :=
  fun m => if Nat.eqb m n then Some v else l m.

Definition entry_locals (args : list value) : locals :=
  fun n => match n with 0 => None | S k => nth_error args k end.

Inductive outcome :=
  | Done (v : value)
  | Diverged
  | Stuck (why : name).

Definition int_bits (w : int_width) : Z :=
  match w with
  | W8 => 8 | W16 => 16 | W32 => 32
  | W64 => 64 | W128 => 128 | WSize => 64
  end.

Definition wrap (t : ty) (z : Z) : option Z :=
  match t with
  | TInt w =>
      let m := Z.pow 2 (int_bits w) in
      let r := Z.modulo z m in
      Some (if Z.ltb r (Z.pow 2 (Z.sub (int_bits w) 1)) then r else Z.sub r m)
  | TUint w => Some (Z.modulo z (Z.pow 2 (int_bits w)))
  | _ => None
  end.

Definition overflows (t : ty) (z : Z) : bool :=
  match t with
  | TInt w =>
      let h := Z.pow 2 (Z.sub (int_bits w) 1) in
      orb (Z.ltb z (Z.opp h)) (Z.leb h z)
  | TUint w => orb (Z.ltb z 0) (Z.leb (Z.pow 2 (int_bits w)) z)
  | _ => true
  end.

Fixpoint read_proj (v : value) (ps : list proj_elem) : option value :=
  match ps with
  | [] => Some v
  | PField i _ :: rest =>
      match v with
      | VTuple vs =>
          match nth_error vs i with
          | Some x => read_proj x rest
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition read_place (l : locals) (p : place) : option value :=
  match l (pl_local p) with
  | Some v => read_proj v (pl_proj p)
  | None => None
  end.

Definition eval_const (c : constant) : option value :=
  match c with
  | KVal (CvScalar (ScInt z _)) TBool => Some (VBool (negb (Z.eqb z 0)))
  | KVal (CvScalar (ScInt z _)) _ => Some (VInt z)
  | KVal CvZeroSized _ => Some VUnit
  | _ => None
  end.

Definition eval_operand (l : locals) (o : operand) : option value :=
  match o with
  | OCopy p | OMove p => read_place l p
  | OConst c => eval_const (co_const c)
  | ORuntimeCheck _ => Some (VBool true)
  end.

Definition elem_ty (t : ty) (i : nat) : ty :=
  match t with
  | TTuple ts => nth i ts (TError "no such field")
  | _ => t
  end.

Definition eval_binop (dst : ty) (op : bin_op) (a b : value) : option value :=
  match a, b with
  | VInt x, VInt y =>
      let arith k :=
        match wrap dst (k x y) with Some z => Some (VInt z) | None => None end in
      let checked k :=
        match wrap (elem_ty dst 0) (k x y) with
        | Some z => Some (VTuple [VInt z; VBool (overflows (elem_ty dst 0) (k x y))])
        | None => None
        end in
      match op with
      | BAdd => arith Z.add
      | BSub => arith Z.sub
      | BMul => arith Z.mul
      | BAddWithOverflow => checked Z.add
      | BSubWithOverflow => checked Z.sub
      | BMulWithOverflow => checked Z.mul
      | BDiv => if Z.eqb y 0 then None else arith Z.quot
      | BRem => if Z.eqb y 0 then None else arith Z.rem
      | BBitAnd => arith Z.land
      | BBitOr => arith Z.lor
      | BBitXor => arith Z.lxor
      | BEq => Some (VBool (Z.eqb x y))
      | BNe => Some (VBool (negb (Z.eqb x y)))
      | BLt => Some (VBool (Z.ltb x y))
      | BLe => Some (VBool (Z.leb x y))
      | BGt => Some (VBool (Z.ltb y x))
      | BGe => Some (VBool (Z.leb y x))
      | _ => None
      end
  | VBool p, VBool q =>
      match op with
      | BEq => Some (VBool (Bool.eqb p q))
      | BNe => Some (VBool (negb (Bool.eqb p q)))
      | BBitAnd => Some (VBool (andb p q))
      | BBitOr => Some (VBool (orb p q))
      | BBitXor => Some (VBool (xorb p q))
      | _ => None
      end
  | _, _ => None
  end.

Definition eval_rvalue (l : locals) (dst : ty) (r : rvalue) : option value :=
  match r with
  | RUse o _ => eval_operand l o
  | RBinaryOp op a b =>
      match eval_operand l a, eval_operand l b with
      | Some x, Some y => eval_binop dst op x y
      | _, _ => None
      end
  | RUnaryOp UNot o =>
      match eval_operand l o with
      | Some (VBool b) => Some (VBool (negb b))
      | Some (VInt z) => match wrap dst (Z.lnot z) with
                         | Some w => Some (VInt w)
                         | None => None
                         end
      | _ => None
      end
  | RUnaryOp UNeg o =>
      match eval_operand l o with
      | Some (VInt z) => match wrap dst (Z.opp z) with
                         | Some w => Some (VInt w)
                         | None => None
                         end
      | _ => None
      end
  | RAggregate AgTuple fs =>
      option_map VTuple
        ((fix go (os : list operand) : option (list value) :=
            match os with
            | [] => Some []
            | o :: rest =>
                match eval_operand l o, go rest with
                | Some v, Some vs => Some (v :: vs)
                | _, _ => None
                end
            end) fs)
  | _ => None
  end.

Definition local_ty (b : body) (n : nat) : ty :=
  match nth_error (bd_locals b) n with
  | Some d => ld_ty d
  | None => TError "no such local"
  end.

Definition exec_stmt (b : body) (l : locals) (s : statement) : option locals :=
  match st_kind s with
  | SAssign p r =>
      match pl_proj p with
      | [] =>
          match eval_rvalue l (local_ty b (pl_local p)) r with
          | Some v => Some (set l (pl_local p) v)
          | None => None
          end
      | _ => None
      end
  | SStorageLive _ | SStorageDead _ | SNop | SConstEvalCounter => Some l
  | SFakeRead _ _ | SAscribeUserType _ _ _ | SPlaceMention _ => Some l
  | SBackwardIncompatibleDropHint _ _ => Some l
  | _ => None
  end.

Fixpoint exec_stmts (b : body) (l : locals) (ss : list statement) : option locals :=
  match ss with
  | [] => Some l
  | s :: rest =>
      match exec_stmt b l s with
      | Some l' => exec_stmts b l' rest
      | None => None
      end
  end.

Inductive transfer :=
  | Goto (bb : block_id)
  | Ret
  | Trap (why : name).

Fixpoint switch_target (z : Z) (ts : list (Z * block_id)) (otherwise : block_id) : block_id :=
  match ts with
  | [] => otherwise
  | (v, t) :: rest => if Z.eqb v z then t else switch_target z rest otherwise
  end.

Definition exec_term (l : locals) (t : terminator) : transfer :=
  match tm_kind t with
  | TGoto n => Goto n
  | TReturn => Ret
  | TSwitchInt d ts o =>
      match eval_operand l d with
      | Some (VInt z) => Goto (switch_target z ts o)
      | Some (VBool bb) => Goto (switch_target (if bb then 1 else 0) ts o)
      | _ => Trap "switchInt on a non-scalar"
      end
  | TAssert c expected _ target _ =>
      match eval_operand l c with
      | Some (VBool bb) =>
          if Bool.eqb bb expected then Goto target else Trap "assertion failed"
      | _ => Trap "assert on a non-boolean"
      end
  | TFalseEdge real _ => Goto real
  | TFalseUnwind real _ => Goto real
  | TUnreachable => Trap "reached unreachable"
  | _ => Trap "terminator outside the fragment"
  end.

Definition find_block (b : body) (n : block_id) : option basic_block :=
  find (fun blk => Nat.eqb (bb_id blk) n) (bd_blocks b).

Fixpoint run (fuel : nat) (b : body) (l : locals) (cur : block_id) : outcome :=
  match fuel with
  | 0 => Diverged
  | S f =>
      match find_block b cur with
      | None => Stuck "no such block"
      | Some blk =>
          match exec_stmts b l (bb_stmts blk) with
          | None => Stuck "statement outside the fragment"
          | Some l' =>
              match exec_term l' (bb_term blk) with
              | Goto n => run f b l' n
              | Trap why => Stuck why
              | Ret =>
                  match l' 0 with
                  | Some v => Done v
                  | None => Stuck "returned without setting the return place"
                  end
              end
          end
      end
  end.

Definition eval_body (fuel : nat) (b : body) (args : list value) : outcome :=
  run fuel b (entry_locals args) 0.

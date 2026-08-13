From RustRocq Require Import Syntax.
From Vmir Require Import Layout Language.
From Vmir.RustcMir Require Syntax.
From Stdlib Require Import String List ZArith.
Import ListNotations.

Local Open Scope string_scope.

Module Rs := Vmir.RustcMir.Syntax.

Definition to_width (w : Syntax.int_width) : Layout.int_width :=
  match w with
  | Syntax.W8 => Layout.W8
  | Syntax.W16 => Layout.W16
  | Syntax.W32 => Layout.W32
  | Syntax.W64 => Layout.W64
  | Syntax.W128 => Layout.W128
  | Syntax.WSize => Layout.WPointer
  end.

Definition to_mut (m : Syntax.mutability) : Layout.mutability :=
  match m with
  | Syntax.Mut => Layout.Mut
  | Syntax.Imm => Layout.Shared
  end.

Fixpoint to_ty (t : Syntax.ty) : option Layout.vmir_ty :=
  let fix tys (ts : list Syntax.ty) : option (list Layout.vmir_ty) :=
    match ts with
    | [] => Some []
    | t :: rest =>
        match to_ty t, tys rest with
        | Some t', Some rest' => Some (t' :: rest')
        | _, _ => None
        end
    end in
  match t with
  | Syntax.TBool => Some Layout.TyBool
  | Syntax.TChar => Some Layout.TyChar
  | Syntax.TStr => Some Layout.TyStr
  | Syntax.TNever => Some Layout.TyNever
  | Syntax.TInt w => Some (Layout.TyInt (to_width w))
  | Syntax.TUint w => Some (Layout.TyUint (to_width w))
  | Syntax.TFloat w =>
      Some (Layout.TyFloat (match w with
                            | Syntax.FW16 => 16 | Syntax.FW32 => 32
                            | Syntax.FW64 => 64 | Syntax.FW128 => 128
                            end))
  | Syntax.TTuple ts =>
      match tys ts with
      | Some ts' => Some (Layout.TyTuple ts')
      | None => None
      end
  | Syntax.TArray e n =>
      match to_ty e, n with
      | Some e', Syntax.CValue _ bits =>
          if Z.leb 0 bits then Some (Layout.TyArray e' (Z.to_nat bits)) else None
      | _, _ => None
      end
  | Syntax.TSlice e =>
      match to_ty e with Some e' => Some (Layout.TySlice e') | None => None end
  | Syntax.TRef _ p m =>
      match to_ty p with
      | Some p' => Some (Layout.TyRef (to_mut m) p')
      | None => None
      end
  | Syntax.TRawPtr p m =>
      match to_ty p with
      | Some p' => Some (Layout.TyRawPtr (to_mut m) p')
      | None => None
      end
  | Syntax.TAdt path _ => Some (Layout.TyAdt path [])
  | _ => None
  end.

Definition to_shape (t : Syntax.ty) : option value_shape :=
  match to_ty t with
  | Some t' => shape_of_layout_ty t'
  | None => None
  end.

Definition to_proj (e : Syntax.proj_elem) : option Rs.rs_projection_elem :=
  match e with
  | Syntax.PDeref => Some Rs.RsProjDeref
  | Syntax.PField i _ => Some (Rs.RsProjField i 0%nat)
  | Syntax.PIndex l => Some (Rs.RsProjIndex l)
  | Syntax.PConstantIndex o m fe => Some (Rs.RsProjConstantIndex o m fe)
  | Syntax.PSubslice f t fe => Some (Rs.RsProjSubslice f t fe)
  | Syntax.PDowncast nm v => Some (Rs.RsProjDowncast nm v)
  | Syntax.POpaqueCast _ => Some Rs.RsProjDeref
  | Syntax.PUnwrapUnsafeBinder _ => None
  end.

Fixpoint to_projs (es : list Syntax.proj_elem) : option (list Rs.rs_projection_elem) :=
  match es with
  | [] => Some []
  | e :: rest =>
      match to_proj e, to_projs rest with
      | Some e', Some rest' => Some (e' :: rest')
      | _, _ => None
      end
  end.

Definition to_place (p : Syntax.place) : option Rs.rs_place :=
  match to_projs (Syntax.pl_proj p) with
  | Some ps => Some (Rs.RsPlace (Syntax.pl_local p) ps)
  | None => None
  end.

Fixpoint packed_offsets (at_ : nat) (ts : list Layout.vmir_ty) : list nat :=
  match ts with
  | [] => []
  | t :: rest =>
      let sz := match shape_of_layout_ty t with
                | Some sh => shape_size_with_layouts [] sh
                | None => 0%nat
                end in
      at_ :: packed_offsets (at_ + sz) rest
  end.

Definition packed_layout (t : Layout.vmir_ty) (sh : value_shape) : type_layout :=
  let fields := match t with
                | Layout.TyTuple ts => ts
                | Layout.TyAdt _ ts => ts
                | _ => []
                end in
  let fl := match t with
            | Layout.TyTuple ts | Layout.TyAdt _ ts =>
                FieldsArbitrary (packed_offsets 0%nat ts)
            | Layout.TyArray e n =>
                FieldsArray (match shape_of_layout_ty e with
                             | Some esh => shape_size_with_layouts [] esh
                             | None => 0%nat
                             end) n
            | _ => FieldsPrimitive
            end in
  TypeLayoutData
              "packed"
              t
            (shape_size_with_layouts [] sh)
           (shape_align_with_layouts [] sh)
     false
     fields
          fl
        (VariantsSingle 0%nat)
             (AbiMemory true).

Fixpoint shapes_of (fuel : nat) (t : Layout.vmir_ty) : list (Layout.vmir_ty * value_shape) :=
  match fuel with
  | 0%nat => []
  | S f =>
      let here := match shape_of_layout_ty t with
                  | Some sh => [(t, sh)]
                  | None => []
                  end in
      let inner :=
        match t with
        | Layout.TyTuple ts => concat (map (shapes_of f) ts)
        | Layout.TyArray e _ | Layout.TySlice e => shapes_of f e
        | Layout.TyRef _ p | Layout.TyRawPtr _ p => shapes_of f p
        | _ => []
        end in
      here ++ inner
  end.

Definition ty_seen (seen : list Layout.vmir_ty) (t : Layout.vmir_ty) : bool :=
  existsb (Layout.vmir_ty_eqb t) seen.

Fixpoint dedup (acc : list Layout.vmir_ty) (xs : list (Layout.vmir_ty * value_shape))
    : list type_layout :=
  match xs with
  | [] => []
  | (t, sh) :: rest =>
      if ty_seen acc t
      then dedup acc rest
      else packed_layout t sh :: dedup (t :: acc) rest
  end.

Definition layouts_of_body (b : Syntax.body) : layout_env :=
  dedup []
    (concat (map (fun d => match to_ty (Syntax.ld_ty d) with
                           | Some t => shapes_of 32%nat t
                           | None => []
                           end)
                 (Syntax.bd_locals b))).

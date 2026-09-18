From RustRocq Require Import Syntax LayoutAlg Memory Denote Lib.Models.
From Stdlib Require Import Bool String List ZArith.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition phys_addr_path : name := "x86_64::PhysAddr".
Definition phys_frame_path : name := "x86_64::structures::paging::PhysFrame".
Definition phys_frame_range_path : name := "x86_64::structures::paging::frame::PhysFrameRange".

Definition phys_addr (a : Z) : runtime_value := VAdt phys_addr_path 0 [VBits W64 a].

Definition phys_frame (a : Z) : runtime_value := VAdt phys_frame_path 0 [phys_addr a; phantom].

Definition phys_frame_range (s e : Z) : runtime_value :=
  VAdt phys_frame_range_path 0 [phys_frame s; phys_frame e].

Definition addr_of (v : runtime_value) : option Z :=
  match v with
  | VAdt p 0 [VBits W64 a] => if String.eqb p phys_addr_path then Some a else None
  | _ => None
  end.

Definition frame_start (v : runtime_value) : option Z :=
  match v with
  | VAdt p 0 [a; _] => if String.eqb p phys_frame_path then addr_of a else None
  | _ => None
  end.

Definition page_size (t : ty) : option Z :=
  match t with
  | TAdt p [] =>
      if String.eqb p "x86_64::structures::paging::Size4KiB" then Some 4096
      else if String.eqb p "x86_64::structures::paging::Size2MiB" then Some (4096 * 512)
      else if String.eqb p "x86_64::structures::paging::Size1GiB" then Some (4096 * 512 * 512)
      else None
  | _ => None
  end.

Definition is_frame_of (t : ty) : option Z :=
  match t with
  | TAdt p [GTy s] => if String.eqb p phys_frame_path then page_size s else None
  | _ => None
  end.

Definition phys_addr_limit : Z := 2 ^ 52.

Definition frame_add (size start n : Z) : M result :=
  let m := n * size in
  if u64_limit <=? m then panics
  else
    let a := start + m in
    if u64_limit <=? a then panics
    else if phys_addr_limit <=? a then panics
    else returned (phys_frame (a - a mod size)).

Section X86_64.

Context `{Alg : LayoutAlg}.

Definition compare_frames (adts : list adt_def) (frame : ty) (k : Z -> Z -> bool)
    (x y : runtime_value) : M result :=
  fx <- read_arg adts frame x ;;
  fy <- read_arg adts frame y ;;
  match frame_start fx, frame_start fy with
  | Some a, Some b => returned (VBool (k a b))
  | _, _ => fail "a frame comparison on values that are not frames"
  end.

Definition x86_64_model : partial_model := fun adts f targs vs =>
  if String.eqb f "x86_64::structures::paging::PageSize::SIZE" then
    Some match targs, vs with
         | [GTy s], [] =>
             match page_size s with
             | Some z => returned (VBits W64 z)
             | None => fail "PageSize::SIZE of an unknown page size"
             end
         | _, _ => fail "PageSize::SIZE with unexpected arguments"
         end
  else if String.eqb f "x86_64::structures::paging::PhysFrame::<S>::start_address" then
    Some match vs with
         | [fr] =>
             match frame_start fr with
             | Some a => returned (phys_addr a)
             | None => fail "PhysFrame::start_address of a value that is not a frame"
             end
         | _ => fail "PhysFrame::start_address with unexpected arguments"
         end
  else if String.eqb f "x86_64::PhysAddr::as_u64" then
    Some match vs with
         | [a] =>
             match addr_of a with
             | Some z => returned (VBits W64 z)
             | None => fail "PhysAddr::as_u64 of a value that is not an address"
             end
         | _ => fail "PhysAddr::as_u64 with unexpected arguments"
         end
  else if String.eqb f "x86_64::structures::paging::PhysFrame::<S>::range" then
    Some match vs with
         | [s; e] =>
             match frame_start s, frame_start e with
             | Some a, Some b => returned (phys_frame_range a b)
             | _, _ => fail "PhysFrame::range of values that are not frames"
             end
         | _ => fail "PhysFrame::range with unexpected arguments"
         end
  else if String.eqb f "core::ops::Add::add" then
    match targs, vs with
    | [GTy t; GTy (TUint W64)], [fr; VBits W64 n] =>
        match is_frame_of t with
        | Some size =>
            Some match frame_start fr with
                 | Some a => frame_add size a n
                 | None => fail "PhysFrame + u64 on a value that is not a frame"
                 end
        | None => None
        end
    | _, _ => None
    end
  else if String.eqb f "core::cmp::PartialOrd::lt" then
    match targs, vs with
    | [GTy t; GTy _], [x; y] =>
        match is_frame_of t with
        | Some _ => Some (compare_frames adts t Z.ltb x y)
        | None => None
        end
    | _, _ => None
    end
  else if String.eqb f "core::cmp::PartialOrd::gt" then
    match targs, vs with
    | [GTy t; GTy _], [x; y] =>
        match is_frame_of t with
        | Some _ => Some (compare_frames adts t (fun a b => Z.ltb b a) x y)
        | None => None
        end
    | _, _ => None
    end
  else None.

End X86_64.

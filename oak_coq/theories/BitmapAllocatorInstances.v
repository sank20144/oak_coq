Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From XY Require Import PhysicalMemory.
From XY Require Import BitArr.
From XY Require Import BitmapAllocatorCore.

(** * Common Page Sizes *)

Definition size_4k : PageSize := {|
  size := 4096%Z;
  size_positive := eq_refl
|}.

Definition size_2m : PageSize := {|
  size := 2097152%Z;
  size_positive := eq_refl
|}.

Definition page_size_2m : Z := 2097152%Z.

(** * Example Physical Frame Ranges *)

Definition range_0_32m : PhysFrameRange size_2m.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 33554432%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_0_8k : PhysFrameRange size_4k.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 8192%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_0_128k : PhysFrameRange size_4k.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 131072%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined. 

Definition range_0_512gb : PhysFrameRange size_2m.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 549755813888%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

(** * Example Allocator Instances *)

Definition marked_allocator_0_8k : BitmapAllocator size_4k :=
  match mark_valid (new_allocator range_0_8k) range_0_8k true with
  | Some alloc => alloc
  | None => new_allocator range_0_8k
  end.

Definition marked_allocator_0_128k : BitmapAllocator size_4k :=
  match mark_valid (new_allocator range_0_128k) range_0_128k true with
  | Some alloc => alloc
  | None => new_allocator range_0_128k
  end.

Definition marked_allocator_0_32m : BitmapAllocator size_2m :=
  match mark_valid (new_allocator range_0_32m) range_0_32m true with
  | Some alloc => alloc
  | None => new_allocator range_0_32m
  end.

Definition marked_allocator_0_512gb : BitmapAllocator size_2m :=
  match mark_valid (new_allocator range_0_512gb) range_0_512gb true with
  | Some alloc => alloc
  | None => new_allocator range_0_512gb
  end.

(** * Example Computation *)

Compute let alloc := marked_allocator_0_128k in
  match allocate_frame alloc with
  | Some (frame1, alloc1) => 
      (start_address _ frame1,
       match allocate_frame alloc1 with
       | Some (frame2, alloc2) => 
           (start_address _ frame2, 
            allocated _ alloc2)
       | None => ((-1)%Z, [])
       end)
  | None => ((-1)%Z, ((-1)%Z, []))
  end.

(** * Example Bitmap Allocator Instance for Oak restricted kernel *)

Compute let alloc := marked_allocator_0_512gb in
  match allocate_frame alloc with
  | Some (frame1, alloc1) => 
      (start_address _ frame1,
       match allocate_frame alloc1 with
       | Some (frame2, alloc2) => 
           (start_address _ frame2, 
            allocated _ alloc2)
       | None => ((-1)%Z, [])
       end)
  | None => ((-1)%Z, ((-1)%Z, []))
  end.
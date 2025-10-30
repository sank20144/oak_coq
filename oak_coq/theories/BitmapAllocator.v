Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

From OC Require Import VariableModel.
From OC Require Import BitArr.
From OC Require Import PhysicalMemory.
From OC Require Import BitmapAllocatorCore.

(** Axioms for converting BitmapAllocator to/from value *)
Axiom bitmap_allocator_to_value : forall {S : PageSize} {n : nat}, 
    BitmapAllocator S n -> value.

Axiom value_to_bitmap_allocator : forall {S : PageSize} {n : nat}, 
    value -> option (BitmapAllocator S n).

Axiom bitmap_allocator_roundtrip : forall {S : PageSize} {n : nat} (alloc : BitmapAllocator S n),
    value_to_bitmap_allocator (bitmap_allocator_to_value alloc) = Some alloc.

Notation "'let!' x '←' m ';' f" := 
  (match m with Some x => f | None => None end)
  (at level 200, x pattern, m at level 100, f at level 200, right associativity).

Notation "'return!' e" := (Some e) (at level 200).

(** * Core Allocator Operations *)

(** Initialize a new bitmap allocator as an owned variable *)
Definition init_allocator {S : PageSize} {n : nat}
    (s : prog_state) (alloc_var : var_name) (r : PhysFrameRange S) (lifetime_end : nat)
    : option (prog_state * addr) :=
  let alloc := mkBitmapAllocator S n (make_bitarray n) (make_bitarray n) r in
  let_owned s alloc_var (bitmap_allocator_to_value alloc) lifetime_end.

Definition mark_valid {S : PageSize} {n : nat}
    (s : prog_state) (alloc_var : var_name) (temp_ref : var_name)
    (frame_range : PhysFrameRange S) (is_valid : bool) (borrow_end : nat)
    : option prog_state :=
  (* Create mutable borrow *)
  let! s1 ← let_mut_ref s temp_ref alloc_var borrow_end;
  
  let! alloc_val ← read_var s1 temp_ref;
  let! alloc ← value_to_bitmap_allocator alloc_val;
  
  let! start_idx ← frame_to_idx alloc (start_frame S frame_range);
  let! end_idx ← frame_to_idx alloc (end_frame S frame_range);
  
  let new_valid := set_bit_range (valid S n alloc) start_idx end_idx is_valid in
  let alloc' := mkBitmapAllocator S n (allocated S n alloc) new_valid (range S n alloc) in
  
  let! s2 ← write_var s1 temp_ref (bitmap_allocator_to_value alloc');
  
  drop_var s2 temp_ref.

(* unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for BitmapAllocator<S, N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?;
        self.allocated.set(frame_idx, true);
        self.frame(frame_idx)
    }
}
*)
(** Allocate a single frame - takes mutable reference *)
Definition allocate_frame {S : PageSize} {n : nat}
    (s : prog_state) (alloc_var : var_name) (temp_ref : var_name) (borrow_end : nat)
    : option (prog_state * PhysFrame S) :=
  (* Create mutable borrow *)
  let! s1 ← let_mut_ref s temp_ref alloc_var borrow_end;
  
  let! alloc_val ← read_var s1 temp_ref;
  let! alloc ← value_to_bitmap_allocator alloc_val;
  
  let available := bitand (valid S n alloc) (bitnot (allocated S n alloc)) in
  
  let! frame_idx ← first_one_from_zero available;
  let! frame ← idx_to_frame alloc frame_idx;
  
  let new_allocated := set_bit (allocated S n alloc) frame_idx true in
  let alloc' := mkBitmapAllocator S n new_allocated (valid S n alloc) (range S n alloc) in
  
  let! s2 ← write_var s1 temp_ref (bitmap_allocator_to_value alloc');
  
  let! s3 ← drop_var s2 temp_ref;
  return! (s3, frame).

(** Deallocate a frame - takes mutable reference *)
Definition deallocate_frame {S : PageSize} {n : nat}
    (s : prog_state) (alloc_var : var_name) (temp_ref : var_name)
    (frame : PhysFrame S) (borrow_end : nat)
    : option prog_state :=
  (* Create mutable borrow *)
  let! s1 ← let_mut_ref s temp_ref alloc_var borrow_end;
  
  let! alloc_val ← read_var s1 temp_ref;
  let! alloc ← value_to_bitmap_allocator alloc_val;
  
  let! frame_idx ← frame_to_idx alloc frame;
  
  if get_bit (valid S n alloc) frame_idx && get_bit (allocated S n alloc) frame_idx then
    
    let new_allocated := set_bit (allocated S n alloc) frame_idx false in
    let alloc' := mkBitmapAllocator S n new_allocated (valid S n alloc) (range S n alloc) in
    
    let! s2 ← write_var s1 temp_ref (bitmap_allocator_to_value alloc');
    
    drop_var s2 temp_ref
  else None.

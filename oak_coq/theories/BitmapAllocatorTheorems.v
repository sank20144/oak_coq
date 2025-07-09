Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.
From OC Require Import BitmapAllocatorCore.
From OC Require Import BitArrLemmas.

(** * Theorems and Properties *)

Theorem allocate_frame_preserves_wf:
   forall {S : PageSize} {n : nat} (alloc : BitmapAllocator S n),
  allocator_wf alloc ->
  match allocate_frame alloc with
  | Some (_, alloc') => allocator_wf alloc'
  | None => True
  end.
Proof.
  intros.
  unfold allocate_frame.
  destruct (first_one_from_zero (get_available alloc)) as [idx|] eqn:Hfirst.
  - destruct (idx_to_frame alloc idx) as [frame|] eqn:Hidx_to_frame.
    + simpl. unfold allocator_wf.
      intros idx' H_bound H_allocated'.
      destruct (Nat.eq_dec idx' idx) as [Heq|Hneq].
      * subst idx'.
        simpl.
        assert (H_available: get_bit (get_available alloc) idx = true).
        {
          apply first_one_returns_true with (bits := get_available alloc).
          exact Hfirst.
        }
        unfold get_available in H_available.
        rewrite bitand_get_bit in H_available.
        
        destruct (get_bit (valid S n alloc) idx) eqn:H_valid_idx.
        -- reflexivity.
        -- simpl in H_available.
           discriminate H_available.
        
      * simpl.

        apply H.
        -- exact H_bound.
        -- assert (H_different: get_bit (set_bit (allocated S n alloc) idx true) idx' = 
                                get_bit (allocated S n alloc) idx').
           {
             apply get_bit_set_bit_different.
             - exact H_bound.
             - symmetry. exact Hneq.
           }
           rewrite <- H_different.
           simpl in *.
           exact H_allocated'.
      + trivial.
    - trivial.
Qed.

Theorem deallocate_frame_preserves_wf: forall (S : PageSize) (n : nat) 
        (alloc : BitmapAllocator S n) (frame : PhysFrame S),
  allocator_wf alloc ->
  match deallocate_frame alloc frame with
  | Some alloc' => allocator_wf alloc'
  | None => True
  end.

(** Allocation fails when no frames are available *)
Theorem allocate_frame_failure {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) :
  allocator_wf alloc ->
  allocate_frame alloc = None ->
  num_available alloc = 0.

(** Allocation returns a valid, previously unallocated frame *)
Theorem allocate_frame_correctness {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
        (frame : PhysFrame S) (alloc' : BitmapAllocator S n) :
  allocator_wf alloc ->
  allocate_frame alloc = Some (frame, alloc') ->
  (** The returned frame was available before allocation *)
  (match frame_to_idx alloc frame with
   | Some idx => get_bit (valid S n alloc) idx = true /\
                 get_bit (allocated S n alloc) idx = false
   | None => False
   end) /\
  (** The returned frame is now allocated *)
  (match frame_to_idx alloc' frame with
   | Some idx => get_bit (allocated S n alloc') idx = true
   | None => False
   end) /\
  (** Frame is within the allocator's range *)
  is_frame_valid alloc frame = true.

(** Deallocation succeeds only for allocated, valid frames *)
Theorem deallocate_frame_precondition {S : PageSize} {n : nat} 
        (alloc : BitmapAllocator S n) (frame : PhysFrame S) (alloc' : BitmapAllocator S n) :
  allocator_wf alloc ->
  deallocate_frame alloc frame = Some alloc' ->
  is_frame_allocated alloc frame = true /\
  is_frame_valid alloc frame = true.

  (** No double allocation: allocate_frame never returns an already allocated frame *)
Theorem no_double_allocation {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
        (f : PhysFrame S) (returned_frame : PhysFrame S) (new_alloc : BitmapAllocator S n) (idx : nat) :
  allocator_wf alloc ->
  is_frame_allocated alloc f = true ->
  allocate_frame alloc = Some (returned_frame, new_alloc) ->
  f <> returned_frame.
Proof.
  
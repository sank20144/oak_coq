Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From XY Require Import PhysicalMemory.
From XY Require Import BitArr.
From XY Require Import BitmapAllocatorCore.
From XY Require Import BitmapAllocatorLemmas.

(** * Theorems and Properties *)

(** A newly created allocator has no allocated frames *)
Theorem new_allocator_no_alloc : forall {S : PageSize} (r : PhysFrameRange S),
  count_ones (allocated S (new_allocator r)) = 0.
Proof.
  intros S r.
  unfold new_allocator.
  simpl.
  induction (Z.to_nat ((start_address S (end_frame S r) - start_address S (start_frame S r)) / size S)); simpl; auto.
Qed.

(** After allocating a frame, the number of allocated frames increases by 1 *)
Theorem allocate_frame_increases_count : forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  allocate_frame alloc = Some (frame, new_alloc) ->
  count_ones (allocated S new_alloc) = count_ones (allocated S alloc) + 1.
Proof.
  intros S alloc frame new_alloc H_alloc.
  unfold allocate_frame in H_alloc.
 
  destruct (first_one_from_zero (available alloc)) eqn:H_first; [|discriminate].
  destruct (frame_at_idx alloc n) eqn:H_frame; [|discriminate].
  injection H_alloc as H_eq1 H_eq2.

  assert (H_avail_true: get_bit (available alloc) n = true).
  {
    unfold first_one_from_zero in H_first.
    apply first_one_returns_true in H_first.
    assumption.
  }
  
  assert (H_not_allocated: get_bit (allocated S alloc) n = false).
  {
    rewrite available_correct in H_avail_true.
    apply Bool.andb_true_iff in H_avail_true.
    destruct H_avail_true as [_ H_neg].
    apply Bool.negb_true_iff in H_neg. assumption.
  }

  assert (H_idx_bound: n < length (allocated S alloc)).
  {
    apply first_one_in_bounds in H_first.
    rewrite <- available_length_eq.
    assumption.
  }
  rewrite <- H_eq2. 
  apply set_bit_false_to_true_increases_count; assumption.
Qed.

(** After deallocating a frame, the number of allocated frames decreases by 1 *)
Theorem deallocate_frame_decreases_count : forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  deallocate_frame alloc frame = Some new_alloc ->
  count_ones (allocated S new_alloc) = count_ones (allocated S alloc) - 1.
Proof.
  intros S alloc frame new_alloc H_dealloc.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) eqn:H_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_eq.
  
  assert (H_frame_valid: get_bit (valid S alloc) n = true).
  {
    apply Bool.negb_false_iff in H_valid. assumption.
  }
  
  assert (H_frame_allocated: get_bit (allocated S alloc) n = true).
  {
    apply Bool.negb_false_iff in H_allocated. assumption.
  }
  
  assert (H_idx_bound: n < length (allocated S alloc)).
  { unfold get_bit in H_frame_valid.
    destruct (n <? length (valid S alloc)) eqn:H_n_bound.
    - apply Nat.ltb_lt in H_n_bound.
      rewrite (bitmap_size_ok S alloc).
      exact H_n_bound.
    - apply Nat.ltb_ge in H_n_bound.
      rewrite nth_overflow in H_frame_valid.
      + discriminate H_frame_valid.
      + exact H_n_bound.
  }
  
  rewrite <- H_eq.
  apply set_bit_true_to_false_decreases_count; assumption.
Qed.

(* A frame can only be allocated if it is valid and not already allocated *)
Theorem frame_allocation_valid_unallocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  allocate_frame alloc = Some (frame, new_alloc) ->
  exists idx, 
  frame_idx alloc frame = Some idx /\
  get_bit (valid S alloc) idx = true /\
  get_bit (allocated S alloc) idx = false.
Proof.
  intros S alloc frame new_alloc H_alloc.
  unfold allocate_frame in H_alloc.
  
  destruct (first_one_from_zero (available alloc)) as [n|] eqn:H_first; [|discriminate].
  
  destruct (frame_at_idx alloc n) as [f|] eqn:H_frame; [|discriminate].
  
  injection H_alloc as H_frame_eq H_alloc_eq.
  subst frame.

  exists n.
  
  split.
  - apply frame_at_idx_frame_idx_inverse.
    exact H_frame.
    
  - split. 
    assert (H_avail: get_bit (available alloc) n = true).
    { apply first_one_returns_true. exact H_first. }
    
    unfold available in H_avail.
    rewrite bitand_get_bit in H_avail.
    + destruct (get_bit (valid S alloc) n) eqn:H_valid.
      * reflexivity.
      * simpl in H_avail. discriminate H_avail.
    + apply eq_sym.
      rewrite length_bitnot.
      apply bitmap_size_ok.
    + assert (H_avail: get_bit (available alloc) n = true).
      { apply first_one_returns_true. exact H_first. }
      rewrite available_correct in H_avail.
      apply Bool.andb_true_iff in H_avail.
      destruct H_avail as [_ H_neg].
      apply Bool.negb_true_iff in H_neg.
      exact H_neg.
Qed.
    
(* A frame can only be deallocated if its valid and allocated *)
Theorem frame_deallocation_valid_allocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  deallocate_frame alloc frame = Some new_alloc ->
  exists idx, 
  frame_idx alloc frame = Some idx /\
  get_bit (valid S alloc) idx = true /\
  get_bit (allocated S alloc) idx = true.
Proof.
  intros S alloc frame new_alloc H_dealloc.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) as [n|] eqn:H_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_new_alloc_eq.
  
  exists n.
  
  split.
  - reflexivity.
  
  - split.
    + apply Bool.negb_false_iff in H_valid. exact H_valid.
    + apply Bool.negb_false_iff in H_allocated. exact H_allocated.
Qed.

(* A deallocated frame changes the new bitmaps allocated index to false *)
Theorem deallocate_frame_changes_allocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc idx,
  deallocate_frame alloc frame = Some new_alloc ->
  frame_idx alloc frame = Some idx ->
  get_bit (allocated S new_alloc) idx = false.
Proof.
  intros S alloc frame new_alloc idx H_dealloc H_idx.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) as [n|] eqn:H_frame_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_new_alloc_eq.
  
  assert (H_idx_eq: n = idx).
  {
    injection H_idx as H_idx_eq.
    exact H_idx_eq.
  }
  
  rewrite <- H_idx_eq.
  rewrite <- H_new_alloc_eq.
  simpl.
  
  assert (H_idx_bound: n < length (allocated S alloc)).
  {
    apply Bool.negb_false_iff in H_allocated.
    unfold get_bit in H_allocated.
    destruct (n <? length (allocated S alloc)) eqn:H_bound.
    - apply Nat.ltb_lt in H_bound. exact H_bound.
    - apply Nat.ltb_ge in H_bound.
      rewrite nth_overflow in H_allocated.
      + discriminate H_allocated.
      + exact H_bound.
  }
  
  apply get_bit_set_bit_same.
  exact H_idx_bound.
Qed.

Theorem allocate_frame_preserves_valid : 
  forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc idx,
  allocate_frame alloc = Some (frame, new_alloc) ->
  frame_idx alloc frame = Some idx ->
  get_bit (valid S alloc) idx = get_bit (valid S new_alloc) idx.
Proof.
  intros S alloc frame new_alloc idx H_alloc H_idx.
  unfold allocate_frame in H_alloc.
  destruct (first_one_from_zero (available alloc)) eqn:H_first; [|discriminate].
  destruct (frame_at_idx alloc n) eqn:H_frame; [|discriminate].
  injection H_alloc as H_frame_eq H_alloc_eq.
  subst frame new_alloc.
  simpl.
  reflexivity.
Qed.

(** A frame cannot be allocated twice without being deallocated *)
Theorem no_double_allocation : 
  forall {S : PageSize} (alloc : BitmapAllocator S) (f : PhysFrame S) (returned_frame : PhysFrame S) (new_alloc : BitmapAllocator S) (idx : nat),
  frame_idx alloc f = Some idx ->
  get_bit (allocated S alloc) idx = true ->
  allocate_frame alloc = Some (returned_frame, new_alloc) ->
  f <> returned_frame.
Proof.
  intros S alloc f returned_frame new_alloc idx H_f_idx H_f_bit_allocated H_alloc_result.
  intro H_eq.

  assert (H_returned_not_allocated: exists idx_ret, 
    frame_idx alloc returned_frame = Some idx_ret /\
    get_bit (valid S alloc) idx_ret = true /\
    get_bit (allocated S alloc) idx_ret = false).
  {
    apply frame_allocation_valid_unallocated with (new_alloc := new_alloc).
    exact H_alloc_result.
  }
  
  destruct H_returned_not_allocated as [idx_ret [H_ret_idx [H_ret_valid H_ret_not_allocated]]].

  assert (H_idx_eq: idx = idx_ret).
  {
    rewrite H_eq in H_f_idx.
    assert (H_same_idx: frame_idx alloc returned_frame = Some idx).
    { exact H_f_idx. }
    rewrite H_ret_idx in H_same_idx.
    injection H_same_idx as H_eq_idx.
    symmetry. exact H_eq_idx.
  }

  rewrite H_idx_eq in H_f_bit_allocated.
  rewrite H_f_bit_allocated in H_ret_not_allocated.
  discriminate H_ret_not_allocated.
Qed.
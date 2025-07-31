Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Lia.
Import ListNotations.
From stdpp Require Import bitvector.
From OC Require Import BitArr.
From OC Require Import PhysicalMemory.
From OC Require Import BitmapAllocatorCore.
From OC Require Import BitArrLemmas.


(* Lemmas on bitmap and bitarr ops*)

Local Open Scope Z_scope.

Lemma add_no_overflow a b :
  0 <= to_Z a ->
  0 <= to_Z b ->
  to_Z a + to_Z b < wB ->
  to_Z (a + b) = to_Z a + to_Z b.
Proof.
  intros Ha Hb Hsum.
  rewrite add_spec.
  rewrite Zmod_small; auto.
  split; [lia | exact Hsum].
Qed.

Lemma sub_no_underflow a b :
  to_Z b <= to_Z a ->
  to_Z (a - b) = to_Z a - to_Z b.
Proof.
  intros H.
  rewrite sub_spec.
  rewrite Zmod_small; auto.
  pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b).
  split; lia.
Qed.

Lemma mul_no_overflow a b :
  0 <= to_Z a ->
  0 <= to_Z b ->
  to_Z a * to_Z b < wB ->
  to_Z (a * b) = to_Z a * to_Z b.
Proof.
  intros Ha Hb Hprod.
  rewrite mul_spec.
  rewrite Zmod_small; auto.
  split; [apply Z.mul_nonneg_nonneg; auto | exact Hprod].
Qed.

Lemma div_exact a b :
  to_Z b <> 0 ->
  to_Z a = to_Z b * Z.of_nat (Z.to_nat (to_Z a / to_Z b)) ->
  to_Z (a / b) = to_Z a / to_Z b.
Proof.
  intros Hb Hexact.
  rewrite div_spec.
  reflexivity.
Qed.

Local Close Scope Z_scope.


Lemma first_one_none_implies_count_zero {n : nat} (bits : BitArray n) :
  first_one_from_zero bits = None ->
  count_ones bits = 0%nat.
Proof.
  intros Hnone.
  unfold count_ones.
  assert (Hall_false: forall i, i < n * u64_bits -> 
                      Z.testbit (bv_unsigned bits) (Z.of_nat i) = false).
  {
    intros i Hi.
    unfold first_one_from_zero in Hnone.
    apply find_none with (x := i) in Hnone.
    - exact Hnone.
    - apply in_seq.
      split; [lia | exact Hi].
    
  }
  
  assert (Hhelper: count_ones_helper bits 0 (n * u64_bits) 0 = 0%nat).
  {
    assert (Hgen: forall start remaining acc,
              (forall i, start <= i < start + remaining -> 
               Z.testbit (bv_unsigned bits) (Z.of_nat i) = false) ->
              count_ones_helper bits start remaining acc = acc).
    {
      intros start remaining.
      revert start.
      induction remaining as [|remaining' IH]; intros start acc Hfalse.
      - reflexivity.
      - simpl.
        rewrite Hfalse; [|lia].
        apply IH.
        intros i Hi.
        apply Hfalse.
        lia.
    }
    
    apply Hgen.
    intros i Hi.
    apply Hall_false.
    lia.
  }
  
  exact Hhelper.
Qed.


(** Lemma: frame_to_idx and idx_to_frame are left inverses *)
Lemma frame_to_idx_idx_to_frame_inverse {S : PageSize} {n : nat} 
      (alloc : BitmapAllocator S n) (idx : nat) :
  idx < n * u64_bits -> 
  match idx_to_frame alloc idx with
  | Some frame => frame_to_idx alloc frame = Some idx
  | None => True
  end.
Proof.
Admitted.

(** Lemma: idx_to_frame respects bounds *)
Lemma idx_to_frame_some_implies_valid_idx {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (idx : nat) (frame : PhysFrame S) :
  idx_to_frame alloc idx = Some frame ->
  idx < n * u64_bits.
Proof.
  Admitted.

(** Helper lemma: frame_to_idx is independent of allocated bitmap *)
Lemma frame_to_idx_independent_of_allocated {S : PageSize} {n : nat} 
      (alloc1 alloc2 : BitmapAllocator S n) (frame : PhysFrame S) :
  valid S n alloc1 = valid S n alloc2 ->
  range S n alloc1 = range S n alloc2 ->
  frame_to_idx alloc1 frame = frame_to_idx alloc2 frame.
Proof.
  intros Hvalid Hrange.
  unfold frame_to_idx.
  rewrite Hrange.
  reflexivity.
Qed.

(** Lemma: setting a range of bits preserves true bits *)
Lemma set_bit_range_preserves_true_bits {n : nat} (bits : BitArray n) 
      (start_idx end_idx idx : nat) :
  get_bit bits idx = true ->
  idx < n * u64_bits ->
  get_bit (set_bit_range bits start_idx end_idx true) idx = true.
Proof.
  intros Htrue Hbound.
  unfold set_bit_range.
  
  assert (H_general: forall (initial_bits : BitArray n) (indices : list nat),
    get_bit initial_bits idx = true ->
    get_bit (fold_left (fun acc i => set_bit acc i true) indices initial_bits) idx = true).
  {
    intros initial_bits indices.
    revert initial_bits.
    induction indices as [|i rest IH]; intros initial_bits Hinit_true.
    - simpl. exact Hinit_true.
    - simpl.
      apply IH.
      destruct (Nat.eq_dec idx i) as [Heq|Hneq].
      + subst i.
        apply get_bit_set_bit_same.
        exact Hbound.
      + rewrite get_bit_set_bit_different; auto.
  }
  
  apply H_general.
  exact Htrue.
Qed.

Lemma mark_valid_preserves_wf {S : PageSize} {n : nat} 
      (alloc : BitmapAllocator S n) (frame_range : PhysFrameRange S) :
  allocator_wf alloc ->
  match mark_valid alloc frame_range true with
  | Some alloc' => allocator_wf alloc'
  | None => True
  end.
Proof.
  intros Hwf.
  unfold mark_valid.
  
  destruct (frame_to_idx alloc (start_frame S frame_range)) as [start_idx|] eqn:Hstart;
    [|trivial].
  destruct (frame_to_idx alloc (end_frame S frame_range)) as [end_idx|] eqn:Hend;
    [|trivial].
  
  unfold allocator_wf.
  intros idx H_bound H_allocated.
  simpl in H_allocated.
  
  assert (H_valid_original: get_bit (valid S n alloc) idx = true).
  { apply Hwf; assumption. }
  
  simpl.
  apply set_bit_range_preserves_true_bits; assumption.
Qed.



Lemma mark_valid_preserves_no_allocated {S : PageSize} {n : nat} 
      (alloc : BitmapAllocator S n) (frame_range : PhysFrameRange S) (is_valid : bool) :
  (forall idx, idx < n * u64_bits -> get_bit (allocated S n alloc) idx = false) ->
  match mark_valid alloc frame_range is_valid with
  | Some alloc' => forall idx, idx < n * u64_bits -> get_bit (allocated S n alloc') idx = false
  | None => True
  end.
Proof.
  intros H_no_alloc.
  unfold mark_valid.
  destruct (frame_to_idx alloc (start_frame S frame_range)) as [start_idx|]; [|trivial].
  destruct (frame_to_idx alloc (end_frame S frame_range)) as [end_idx|]; [|trivial].
  
  intros idx H_bound.
  simpl.
  exact (H_no_alloc idx H_bound).
Qed.


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
Proof.
  intros S n alloc frame Hwf.
  unfold deallocate_frame.
  destruct (frame_to_idx alloc frame) as [idx|] eqn:Hidx.
  - destruct (get_bit (valid S n alloc) idx && get_bit (allocated S n alloc) idx) eqn:Hbits.
    + simpl. unfold allocator_wf.
      intros idx' Hbound Halloc'.
      destruct (Nat.eq_dec idx' idx) as [Heq|Hneq].
      * subst idx'.
        apply andb_prop in Hbits as [Hvalid _]. simpl in *.
        exact Hvalid.
      * assert (Hgetbit: get_bit (set_bit (allocated S n alloc) idx false) idx' = get_bit (allocated S n alloc) idx').
        { apply get_bit_set_bit_different; auto. }
        simpl in *.
        apply Hwf; auto.
        rewrite <- Hgetbit. 
        assumption.
    + trivial.
  - trivial.
Qed.
(** Helper lemma: first_one_from_zero returns indices within bounds *)
Lemma first_one_from_zero_lt {n : nat} (bits : BitArray n) (idx : nat) :
  first_one_from_zero bits = Some idx ->
  idx < n * u64_bits.
Proof.
  intros H.
  unfold first_one_from_zero in H.
  apply find_some in H.
  destruct H as [Hrange _].
  apply in_seq in Hrange.
  exact (proj2 Hrange).
Qed.
Lemma first_one_some_implies_nonzero_count {n : nat} (bits : BitArray n) (idx : nat) :
  first_one_from_zero bits = Some idx ->
  count_ones bits > 0.
Proof.
  intros H.
  assert (H_bit_true: get_bit bits idx = true).
  { apply first_one_returns_true; exact H. }
  
  assert (H_idx_bound: idx < n * u64_bits).
  { apply (first_one_from_zero_lt bits); exact H. }

  destruct (count_ones bits) eqn:Hcount.
  - pose proof (count_ones_zero_all_false bits Hcount idx) as H_bit_false.
    rewrite H_bit_true in H_bit_false.
    discriminate.
  - lia.
Qed.

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
Proof.
  intros Hwf Halloc_some.
  unfold allocate_frame in Halloc_some.
  
  destruct (first_one_from_zero (get_available alloc)) as [idx|] eqn:Hfirst; 
    [|discriminate].
  
  destruct (idx_to_frame alloc idx) as [frame'|] eqn:Hidx_to_frame; 
    [|discriminate].
  
  inversion Halloc_some as [[Hframe_eq Halloc'_eq]]. 
  subst frame'.
  
  assert (Havail: get_bit (get_available alloc) idx = true).
  { apply first_one_returns_true. exact Hfirst. }
  
  unfold get_available in Havail.
  rewrite bitand_get_bit in Havail.
  apply andb_prop in Havail as [Hvalid Hnot_alloc].
  
  rewrite bitnot_get_bit in Hnot_alloc.
  - apply negb_true_iff in Hnot_alloc.
    
    assert (Hidx_bound: idx < n * u64_bits).
    { apply first_one_from_zero_lt with (bits := get_available alloc). exact Hfirst. }
    
    assert (Hframe_to_idx: frame_to_idx alloc frame = Some idx).
    {
      pose proof (frame_to_idx_idx_to_frame_inverse alloc idx) as Hinv.
      rewrite Hidx_to_frame in Hinv.
      apply Hinv; exact Hidx_bound.
    }
    split; [|split].
    
    + rewrite Hframe_to_idx.
      split; assumption.
    
    + simpl.
      assert (Hframe_to_idx': frame_to_idx 
               {| allocated := set_bit (allocated S n alloc) idx true;
                  valid := valid S n alloc;
                  range := range S n alloc |} frame = Some idx).
      {
        unfold frame_to_idx.
        simpl.
        exact Hframe_to_idx.
      }
      
      rewrite Hframe_to_idx'.
      
      simpl.
      apply get_bit_set_bit_same.
      exact Hidx_bound.
    
    + unfold is_frame_valid.
      rewrite Hframe_to_idx.
      exact Hvalid.
      
  - apply first_one_from_zero_lt with (bits := get_available alloc).
    exact Hfirst.
Qed.

(** Deallocation succeeds only for allocated, valid frames *)
Theorem deallocate_frame_precondition {S : PageSize} {n : nat} 
        (alloc : BitmapAllocator S n) (frame : PhysFrame S) (alloc' : BitmapAllocator S n) :
  allocator_wf alloc ->
  deallocate_frame alloc frame = Some alloc' ->
  is_frame_allocated alloc frame = true /\
  is_frame_valid alloc frame = true.
Proof.
  Admitted.

  (** No double allocation: allocate_frame never returns an already allocated frame *)
Theorem no_double_allocation {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
        (f : PhysFrame S) (returned_frame : PhysFrame S) (new_alloc : BitmapAllocator S n) (idx : nat) :
  allocator_wf alloc ->
  is_frame_allocated alloc f = true ->
  allocate_frame alloc = Some (returned_frame, new_alloc) ->
  f <> returned_frame.
Proof.
  intros Hwf Hallocf Halloc.
  pose proof (allocate_frame_correctness alloc returned_frame new_alloc Hwf Halloc) as Halloc_corr.
  destruct Halloc_corr as [Hpre [Hpost Hvalid]].
  destruct (frame_to_idx alloc returned_frame) as [idx_ret|] eqn:Hidx_ret; [|contradiction].
  destruct (frame_to_idx alloc f) as [idx_f|] eqn:Hidx_f.
  - simpl in Hallocf.
    specialize (Hpre).
    destruct Hpre as [Hvalid_ret Hnot_alloc].
    intro Heq. subst f.
    rewrite Hidx_ret in Hidx_f. inversion Hidx_f. subst idx_f.
    unfold is_frame_allocated in Hallocf.
    rewrite Hidx_ret in Hallocf.
    simpl in Hallocf.
    rewrite Hnot_alloc in Hallocf.
    discriminate.
  - simpl in Hallocf; congruence.
Qed.
  
(** A zero-initialized bitmap allocator is well-formed *)
Theorem zero_init_allocator_wf {S : PageSize} {n : nat} (r : PhysFrameRange S) :
  allocator_wf (new_allocator n r).
Proof.
  unfold allocator_wf, new_allocator.
  intros idx H_bound H_allocated.
  
  unfold make_bitarray in H_allocated.
  unfold get_bit in H_allocated.
  
  assert (H_zero: get_bit (make_bitarray n) idx = false).
  {
    unfold get_bit, make_bitarray.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  apply Nat.ltb_lt in H_bound.
  rewrite H_bound in H_allocated.
  
  simpl in *.
  unfold get_bit,make_bitarray in H_zero.
  rewrite H_bound in H_zero.
  
  rewrite H_zero in H_allocated.
  discriminate.
Qed.

(** Marking regions as valid in a zero-initialized allocator preserves well-formedness *)
Theorem zero_init_mark_valid_wf {S : PageSize} {n : nat} 
        (r : PhysFrameRange S) (frame_range : PhysFrameRange S) :
  match mark_valid (new_allocator n r) frame_range true with
  | Some alloc' => allocator_wf alloc'
  | None => True
  end.
Proof.
  assert (H_zero_wf: allocator_wf (new_allocator n r)).
  { apply zero_init_allocator_wf. }
  
  unfold mark_valid.
  destruct (frame_to_idx (new_allocator n r) (start_frame S frame_range)) as [start_idx|]; 
    [|trivial].
  destruct (frame_to_idx (new_allocator n r) (end_frame S frame_range)) as [end_idx|]; 
    [|trivial].
  
  unfold allocator_wf. intros idx H_bound H_allocated.
  
  simpl in H_allocated.
  
  assert (H_zero_alloc: get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    unfold new_allocator, make_bitarray, get_bit.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  simpl in *.
  rewrite H_zero_alloc in H_allocated.
  discriminate.
Qed.

Theorem zero_init_mark_valid_general_wf {S : PageSize} {n : nat} 
        (r : PhysFrameRange S) (frame_range : PhysFrameRange S) (is_valid : bool) :
  match mark_valid (new_allocator n r) frame_range is_valid with
  | Some alloc' => allocator_wf alloc'
  | None => True
  end.
Proof.
  assert (H_zero_wf: allocator_wf (new_allocator n r)).
  { apply zero_init_allocator_wf. }
  
  unfold mark_valid.
  destruct (frame_to_idx (new_allocator n r) (start_frame S frame_range)) as [start_idx|]; 
    [|trivial].
  destruct (frame_to_idx (new_allocator n r) (end_frame S frame_range)) as [end_idx|]; 
    [|trivial].
  
  unfold allocator_wf. intros idx H_bound H_allocated.
  
  simpl in H_allocated.
  
  assert (H_zero_alloc: get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    unfold new_allocator, make_bitarray, get_bit.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  simpl in *.
  rewrite H_zero_alloc in H_allocated.
  discriminate.
Qed.


(* Theorem kernel_init_allocator_wf {S : PageSize} {n : nat} 
        (r : PhysFrameRange S) :
  forall alloc : BitmapAllocator S n,
  (exists ranges : list (PhysFrameRange S),
   fold_left (fun acc range => 
     match acc with
     | Some a => mark_valid a range true
     | None => None
     end) ranges (Some (new_allocator n r)) = Some alloc) ->
  allocator_wf alloc.
Proof.
  intros alloc [ranges Hfold].
  
  assert (H_general: forall (init_alloc : BitmapAllocator S n),
    allocator_wf init_alloc ->
    forall final_alloc,
    (exists remaining_ranges,
     fold_left (fun acc range => 
       match acc with
       | Some a => mark_valid a range true
       | None => None
       end) remaining_ranges (Some init_alloc) = Some final_alloc) ->
    allocator_wf final_alloc).
  {
    intros init_alloc Hinit_wf final_alloc [remaining_ranges Hremaining_fold].
    revert init_alloc final_alloc Hinit_wf Hremaining_fold.
    induction remaining_ranges as [|range rest_ranges IH]; 
    intros init_alloc final_alloc Hinit_wf Hremaining_fold.
    
    - simpl in Hremaining_fold.
      inversion Hremaining_fold. subst final_alloc.
      exact Hinit_wf.
    
    - simpl in Hremaining_fold.
      destruct (mark_valid init_alloc range true) as [intermediate_alloc|] eqn:Hmark. 
      + assert (Hintermediate_wf: allocator_wf intermediate_alloc).
        {
          pose proof (mark_valid_preserves_wf init_alloc range Hinit_wf) as Hpres.
          rewrite Hmark in Hpres.
          exact Hpres.
        }
      
        apply (IH intermediate_alloc final_alloc Hintermediate_wf Hremaining_fold).
      + exfalso.
        assert (H_none_propagates: forall remaining_list,
          fold_left (fun acc range0 => 
            match acc with
            | Some a => @mark_valid S n a range0 true
            | None => None
            end) remaining_list None = None).
        {
          intro remaining_list.
          induction remaining_list as [|range_elem rest IHrest].
          - reflexivity.
          - simpl. exact IHrest.
        }
        
        rewrite H_none_propagates in Hremaining_fold.
        discriminate Hremaining_fold.
  }
  
  apply (H_general (new_allocator n r)).
  - apply zero_init_allocator_wf.
  - exists ranges. exact Hfold.
Qed. *)


Theorem mm_init_allocator_wf {S : PageSize} {n : nat} 
        (r : PhysFrameRange S) (ranges_with_validity : list (PhysFrameRange S * bool)) :
  match fold_left (fun acc range_validity => 
     match acc with
     | Some a => mark_valid a (fst range_validity) (snd range_validity)
     | None => None
     end) ranges_with_validity (Some (new_allocator n r)) with
  | Some alloc => allocator_wf alloc
  | None => True
  end.
Proof.
  assert (H_no_alloc_init: forall idx, idx < n * u64_bits -> 
    get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    intros idx H_bound.
    unfold new_allocator, get_bit, make_bitarray.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  assert (H_general: forall (init_alloc : BitmapAllocator S n) remaining_ranges,
    (forall idx, idx < n * u64_bits -> get_bit (allocated S n init_alloc) idx = false) ->
    match fold_left (fun acc range_validity => 
       match acc with
       | Some a => mark_valid a (fst range_validity) (snd range_validity)
       | None => None
       end) remaining_ranges (Some init_alloc) with
    | Some final_alloc => allocator_wf final_alloc
    | None => True
    end).
  {
    intros init_alloc remaining_ranges.
    revert init_alloc.
    induction remaining_ranges as [|(range, validity) rest_ranges IH]; 
    intros init_alloc H_no_alloc.
    
    - simpl.
      unfold allocator_wf.
      intros idx H_bound H_allocated.
      assert (H_false: get_bit (allocated S n init_alloc) idx = false).
      { apply H_no_alloc; exact H_bound. }
      rewrite H_false in H_allocated.
      discriminate.
    
    - simpl.
      destruct (mark_valid init_alloc range validity) as [intermediate_alloc|] eqn:Hmark.
      + assert (H_intermediate_no_alloc: forall idx, idx < n * u64_bits -> 
          get_bit (allocated S n intermediate_alloc) idx = false).
        {
          pose proof (mark_valid_preserves_no_allocated init_alloc range validity H_no_alloc) as H_pres.
          rewrite Hmark in H_pres.
          exact H_pres.
        }
        
        apply (IH intermediate_alloc H_intermediate_no_alloc).
        
      + assert (H_none_propagates: forall remaining_list,
          fold_left (fun acc range_validity => 
            match acc with
            | Some a => @mark_valid S n a (fst range_validity) (snd range_validity)
            | None => None
            end) remaining_list None = None).
        {
          intro remaining_list.
          induction remaining_list as [|range_elem rest IHrest].
          - reflexivity.
          - simpl. exact IHrest.
        }
        rewrite H_none_propagates.
        trivial.
  }
  
  apply (H_general (new_allocator n r) ranges_with_validity H_no_alloc_init).
Qed.
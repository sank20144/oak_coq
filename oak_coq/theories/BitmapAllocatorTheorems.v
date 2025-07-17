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

(** * Theorems and Properties *)

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
  intros H_bound.
  unfold idx_to_frame.
  assert (H_ltb: (idx <? n * u64_bits) = true) by (apply Nat.ltb_lt; exact H_bound).
  rewrite H_ltb.
  
  unfold frame_to_idx.
  simpl.
  
  set (range_start := start_address S (start_frame S (range S n alloc))).
  set (range_end := start_address S (end_frame S (range S n alloc))).
  set (frame_addr := Uint63.add range_start (of_nat idx * size S)).
  
  assert (H_range: (Uint63.leb range_start frame_addr) && (Uint63.ltb frame_addr range_end) = true).
  {
    apply andb_true_intro.
    split.
    - apply Uint63.leb_spec.
      unfold frame_addr.
      rewrite Uint63.add_spec.
      rewrite Uint63.mul_spec.
      
      admit.
      
    - apply Uint63.ltb_spec.
      unfold frame_addr.
      admit.
  }
  rewrite H_range.
  
  set (offset := Uint63.sub frame_addr range_start).
  
  assert (H_offset: offset = (of_nat idx * size S)%uint63).
  {
    unfold offset, frame_addr.
    assert (H_no_overflow: Z.eqb (to_Z (range_start + of_nat idx * size S)) 
                           (to_Z range_start + to_Z (of_nat idx * size S))).
    {
      admit.
    }
    
    assert (H_sub: to_Z offset = to_Z (of_nat idx * size S)).
    {
      
        admit.
    }
    
    apply to_Z_inj.
    exact H_sub.
  }
  
  assert (H_div: Uint63.div offset (size S) = of_nat idx).
  {
    rewrite H_offset.
    assert (H_div_spec: to_Z (offset / size S) = to_Z (of_nat idx)).
    {
      rewrite H_offset.
      rewrite div_spec.
      rewrite mul_spec.
      
      assert (H_idx_small: Z.ltb (Z.mul (to_Z (of_nat idx)) (to_Z (size S))) wB).
      {
        admit.
      }
      
      admit.
    }
    
    simpl.
    admit.
  }
  
  rewrite H_div.
  
  assert (H_final_bound: Uint63.ltb (of_nat idx) (of_nat (n * u64_bits)) = true).
  {
    admit.
  }
  
  rewrite H_final_bound.
  
  assert (H_to_of_nat: to_nat (of_nat idx) = idx).
  {
    admit. 
  }
  rewrite H_to_of_nat.
  reflexivity.
Admitted.

(** Lemma: idx_to_frame respects bounds *)
Lemma idx_to_frame_some_implies_valid_idx {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (idx : nat) (frame : PhysFrame S) :
  idx_to_frame alloc idx = Some frame ->
  idx < n * u64_bits.
Proof.
  intros H.
  unfold idx_to_frame in H.
  destruct (Nat.ltb idx (n * u64_bits)) eqn:Hlt; [|discriminate].
  apply Nat.ltb_lt in Hlt.
  exact Hlt.
Qed.

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
  
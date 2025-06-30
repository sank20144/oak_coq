Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From XY Require Import PhysicalMemory.
From XY Require Import BitArr.
From XY Require Import BitmapAllocatorCore.

(** * Supporting Lemmas for BitmapAllocator *)

Search (S _ < S _).

Lemma nth_map : forall {A B : Type} (f : A -> B) (l : list A) (n : nat) (d : A),
  nth n (map f l) (f d) = f (nth n l d).
Proof.
  intros A B f l n d.
  generalize dependent n.
  induction l as [|a l' IH]; intros n.
  - destruct n; simpl; reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.

(** Available bits are exactly those that are valid but not allocated *)
Lemma available_correct : forall {S : PageSize} (alloc : BitmapAllocator S) (idx : nat),
  get_bit (available alloc) idx = 
  (get_bit (valid S alloc) idx && negb (get_bit (allocated S alloc) idx)).
Proof.
  intros S alloc idx.
  unfold available, get_bit.
  unfold bitand, bitnot.
  assert (map_preserves_length: forall (A B : Type) (f : A -> B) (l : list A), 
         length (map f l) = length l).
        { 
          intros A B f l. induction l; simpl; auto.
        }
  destruct (idx <? length (valid S alloc)) eqn:H_bound.
  
  - apply Nat.ltb_lt in H_bound.
    rewrite nth_map_andb.
    
    assert (H_eq: length (allocated S alloc) = length (valid S alloc))
      by (apply (bitmap_size_ok S alloc)).
    rewrite nth_combine_default; auto.
    rewrite nth_map_negb. simpl in *.
    rewrite <- H_eq in H_bound.
    rewrite <- Nat.ltb_lt in H_bound.
    rewrite H_bound.
    -- reflexivity.
    -- simpl.
       symmetry.
       rewrite map_preserves_length. assumption.
  - apply Nat.ltb_ge in H_bound.
    assert (nth idx (valid S alloc) false = false).
    { apply nth_overflow. assumption. }
    rewrite H. simpl.
    rewrite nth_overflow.
    -- reflexivity.
    -- simpl.
       assert (length_combine_valid_allocated: length (combine (valid S alloc) (map negb (allocated S alloc))) = length (valid S alloc)).
        {
          rewrite length_combine.
          assert (H_eq: length (allocated S alloc) = length (valid S alloc))
            by (apply (bitmap_size_ok S alloc)).
          
          rewrite map_preserves_length.
          rewrite H_eq. simpl. 
          rewrite Nat.min_l.
          -- reflexivity. 
          -- reflexivity.
        }
  rewrite map_preserves_length.
  rewrite length_combine_valid_allocated.
  assumption.
Qed.

Lemma first_one_ge : forall bs start n,
  first_one bs start = Some n -> n >= start.
Proof.
  intros.
  generalize dependent n.
  generalize dependent start.
  induction bs as [|b bs' IH]; simpl in *.
  - discriminate.
  - destruct b eqn:Eb.
    + simpl in *. intros.
      injection H as H_eq.
      rewrite <- H_eq.
      apply Nat.le_refl.
    + simpl in *. intros.
      apply IH in H.
      lia.
Qed.
      
Lemma first_one_ge_offset : forall (bits : BitArray) (offset n : nat),
  first_one bits offset = Some n -> n >= offset.
Proof.
  intros bits offset n H.
  induction bits as [|b bs IH]; simpl in H.
  - discriminate.
  - destruct b.
    + injection H as H. subst. apply Nat.le_refl.
    + simpl in *. 
      destruct bs as [|b bs'] eqn:Ebs.
      * discriminate.
      * destruct b eqn:Eb.
        -- simpl in H.
           injection H as H_eq.
           rewrite <- H_eq.
           apply le_S, Nat.le_refl.
        -- simpl in *.
           assert (H_ge : n >= S (S offset)).
            { apply (first_one_ge bs' (S (S offset))). exact H. }
           apply Nat.le_trans with (S (S offset)).
           --- apply le_S, le_S, Nat.le_refl.
           --- assumption.          
Qed.

Lemma first_one_predecessor : forall bs start n,
  first_one bs (S start) = Some (S n) -> first_one bs start = Some n.
Proof.
  intros bs start n H.
  generalize dependent n.
  generalize dependent start.
  induction bs as [|b bs' IH].
  - intros start n H.
    simpl in H. discriminate H.
  - intros start n H.
    destruct b.
    + simpl in H.
      injection H as H_eq.
      assert (n = start) by (inversion H_eq; reflexivity).
      subst n.
      simpl. reflexivity.
    + simpl in H.
      simpl.
      apply IH.
      exact H.
Qed.

Lemma first_one_returns_true : forall (bits : BitArray) (n : nat),
  first_one_from_zero bits = Some n -> get_bit bits n = true.
Proof.
  intros bits n H.
  unfold first_one_from_zero in H.
  unfold get_bit.
  generalize dependent n.
  induction bits as [|b bs IH].
  - intros. discriminate.
  - destruct b.
    + destruct n.
      * simpl. reflexivity.
      * simpl in *. discriminate.
    + destruct n.
      * simpl in *.  intros.
        assert (H_ge : 0 >= 1).
        { apply (first_one_ge bs 1). exact H. }
        lia.
      * intros.
        simpl in *.
        assert (H_zero : first_one bs 0 = Some n).
        {
          apply first_one_predecessor with (start := 0).
          exact H.
        }
        apply IH. assumption.    
Qed.

Lemma first_one_length_bound : forall bs start n,
  first_one bs start = Some n -> n < start + length bs.
Proof.
  intros bs start n H.
  generalize dependent n.
  generalize dependent start.
  induction bs as [|b bs' IH].
  - intros start n H.
    simpl in H.
    discriminate H.
    
  - intros start n H.
    destruct b eqn:Eb.
    
    + simpl in H.
      injection H as H_eq.
      rewrite <- H_eq.
      simpl.
      apply Nat.lt_add_pos_r; apply Nat.lt_0_succ.
      
    + simpl in H.
      apply IH in H.
      simpl.
      lia. 
Qed.

Lemma first_one_in_bounds : forall (bits : BitArray) (n : nat),
  first_one_from_zero bits = Some n -> n < length bits.
Proof.
  intros bits n H.
  unfold first_one_from_zero in H.
  induction bits as [|b bs IH]; simpl in H.
  - discriminate.
  - destruct b.
    + destruct n.
      * simpl. lia.
      * discriminate.
    + destruct n.
      * simpl in *. lia.
      * simpl in *.
        assert (H_bound : S n < 1 + length bs).
        {
          apply first_one_length_bound.
          exact H.
        }
        assumption.       
Qed.

Lemma available_length_eq : forall {S : PageSize} (alloc : BitmapAllocator S),
  length (available alloc) = length (allocated S alloc).
Proof.
  intros S alloc.
  unfold available, bitand, bitnot.
  rewrite length_map.
  rewrite length_combine.
  rewrite length_map.
  assert (H_eq: length (allocated S alloc) = length (valid S alloc))
    by (apply (bitmap_size_ok S alloc)).
  rewrite H_eq.
  apply Nat.min_l.
  reflexivity.
Qed.

Lemma frame_at_idx_injective : forall {S : PageSize} (alloc : BitmapAllocator S) i j frame,
  frame_at_idx alloc i = Some frame ->
  frame_at_idx alloc j = Some frame ->
  i = j.
Proof.
  intros S alloc i j frame H_i H_j.
  unfold frame_at_idx in H_i, H_j.
  
  set (start_addr := start_address S (start_frame S (range S alloc))).
  set (end_addr := start_address S (end_frame S (range S alloc))).
  set (max_idx := Z.to_nat ((end_addr - start_addr) / size S)).
  
  destruct (i <? max_idx) eqn:H_i_bound.
  - destruct (j <? max_idx) eqn:H_j_bound.
    + set (addr_i := Z.add start_addr (Z.mul (Z.of_nat i) (size S))) in H_i.
      set (addr_j := Z.add start_addr (Z.mul (Z.of_nat j) (size S))) in H_j.
      unfold max_idx in H_i_bound.
      unfold max_idx in H_j_bound.
      
      unfold end_addr, start_addr in *.

      rewrite H_i_bound in H_i.
      rewrite H_j_bound in H_j.
    
      injection H_i as H_frame_i.
      injection H_j as H_frame_j.
      
      simpl in *.
      assert (H_addr_eq: addr_i = addr_j).
      {
        rewrite <- H_frame_i in H_frame_j.
        injection H_frame_j as H_addr_eq_direct.
        symmetry.
        exact H_addr_eq_direct.
      }
      unfold addr_i, addr_j in H_addr_eq.
      
      assert (H_mul_eq: ((Z.of_nat i) * size S)%Z = ((Z.of_nat j) * size S)%Z).
      {
        apply Z.add_cancel_l with start_addr.
        exact H_addr_eq.
      }
      
      assert (H_of_nat_eq: Z.of_nat i = Z.of_nat j).
      {
        apply Z.mul_cancel_r with (size S).
        - apply Z.neq_sym. apply size_nonzero.
        - exact H_mul_eq.
      }
      apply Nat2Z.inj in H_of_nat_eq.
      exact H_of_nat_eq.
      
    + unfold max_idx in H_i_bound.
      unfold max_idx in H_j_bound.
      unfold end_addr, start_addr in *.

      rewrite H_i_bound in H_i.
      rewrite H_j_bound in H_j.
      discriminate H_j.
      
  - unfold max_idx in H_i_bound.
    unfold end_addr, start_addr in *.
    rewrite H_i_bound in H_i.
    discriminate H_i.
Qed.

Lemma set_bit_makes_unavailable : forall {S : PageSize} (alloc : BitmapAllocator S) idx,
  idx < length (allocated S alloc) ->
  get_bit (valid S alloc) idx = true ->
  get_bit (allocated S alloc) idx = false ->
  get_bit (bitand (valid S alloc) (bitnot (set_bit (allocated S alloc) idx true))) idx = false.
Proof.
  intros S alloc idx H_bound H_valid H_not_alloc.
  rewrite bitand_get_bit.
  - rewrite H_valid.
    rewrite bitnot_get_bit.
    + rewrite get_bit_set_bit_same; [|assumption].
      simpl.
      reflexivity.
    + rewrite set_bit_preserves_length.
      assumption.
  - rewrite length_bitnot.
    rewrite set_bit_preserves_length.
    symmetry.
    apply (bitmap_size_ok S alloc).
Qed.

Lemma frame_at_idx_frame_idx_inverse : forall {S : PageSize} (alloc : BitmapAllocator S) (idx : nat) (frame : PhysFrame S),
  frame_at_idx alloc idx = Some frame ->
  frame_idx alloc frame = Some idx.
Proof.
  intros S alloc idx frame H_at_idx.
  unfold frame_at_idx in H_at_idx.
  unfold frame_idx.
  
  set (start_addr := start_address S (start_frame S (range S alloc))).
  set (end_addr := start_address S (end_frame S (range S alloc))).
  set (max_idx := Z.to_nat ((end_addr - start_addr) / size S)).

  destruct (idx <? Z.to_nat
  ((start_address S (end_frame S (range S alloc)) - start_address S
  (start_frame S (range S alloc))) / size S)) eqn:H_bound in H_at_idx; [|discriminate].
  
  set (computed_addr := Z.add start_addr (Z.mul (Z.of_nat idx) (size S))).
  injection H_at_idx as H_frame_eq.
  
  assert (H_frame_addr: start_address S frame = computed_addr).
  { simpl in H_frame_eq. rewrite <- H_frame_eq. reflexivity. }
  
  rewrite H_frame_addr.
  
  assert (H_not_lt_start: (Z.ltb computed_addr start_addr) = false).
  {
    apply Z.ltb_ge.
    unfold computed_addr.
    assert (H_pos: (0 <= Z.of_nat idx * size S)%Z).
    {
      apply Z.mul_nonneg_nonneg.
      - apply Nat2Z.is_nonneg.
      - destruct S as [sz pos]. simpl. lia.
    }
    lia.
  }
  
  assert (H_not_gt_end: (Z.ltb end_addr computed_addr) = false).
  {
    apply Z.ltb_ge.
    unfold computed_addr, end_addr, start_addr.
    
    apply Nat.ltb_lt in H_bound.
    unfold max_idx in H_bound.
    
    assert (H_idx_bound: (Z.of_nat idx < (end_addr - start_addr) / size S)%Z).
    {
      rewrite <- Z2Nat.id.
      - apply Nat2Z.inj_lt. exact H_bound.
      - apply Z.div_pos.
        + unfold end_addr, start_addr.
          assert (H_range: (start_address S (start_frame S (range S alloc)) <= 
                           start_address S (end_frame S (range S alloc)))%Z).
          { exact (range_valid S (range S alloc)). }
          lia.
        + destruct S as [sz pos]. simpl. lia.
    }
    
    assert (H_mul_bound: (Z.of_nat idx * size S < end_addr - start_addr)%Z).
    {
      assert (H_pos: (0 < size S)%Z).
      { destruct S as [sz pos]. simpl. apply Z.gt_lt_iff. exact pos. }
      
      assert (H_mul: (Z.of_nat idx * size S < (end_addr - start_addr) / size S * size S)%Z).
      {
        apply Z.mul_lt_mono_pos_r.
        - exact H_pos.
        - exact H_idx_bound.
      }
      
      assert (H_div_mul: ((end_addr - start_addr) / size S * size S <= end_addr - start_addr)%Z).
      {
        pose proof (Z.div_mod (end_addr - start_addr) (size S)) as H_div_mod.
        assert (H_nz: size S <> 0%Z) by (apply Z.neq_sym; apply size_nonzero).
        specialize (H_div_mod H_nz).
        
        assert (H_mod_nonneg: (0 <= (end_addr - start_addr) mod size S)%Z).
        { apply Z.mod_pos_bound. exact H_pos. }
        
        lia.
      }
      
      eapply Z.lt_le_trans.
      - exact H_mul.
      - exact H_div_mul.
    }
    
    lia.
  }
  
  rewrite H_not_lt_start, H_not_gt_end.
  simpl.
  unfold computed_addr.
  assert (H_sub_cancel: (start_addr + Z.of_nat idx * size S - start_addr)%Z = (Z.of_nat idx * size S)%Z).
  { lia. }
  rewrite H_sub_cancel.
  rewrite Z.div_mul.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.neq_sym. apply size_nonzero.
Qed.
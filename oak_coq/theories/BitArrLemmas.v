Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.

From stdpp Require Import bitvector.
From OC Require Import BitArr.


(** * Helper Lemmas *)


(** Length of a list created by repeating an element n times equals n *)
Lemma eq_length_repeat {A : Type} (x : A) (n : nat) : length (repeat x n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma get_bit_bounds : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    Uint63.to_nat idx >= (to_nat n) * u64_bits ->
    get_bit bits idx = false.
Proof.
  intros n bits idx H_bound.
  unfold get_bit.
  destruct (Uint63.to_nat idx <? (to_nat n) * u64_bits) eqn:H_lt.
  - apply Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

Axiom bitarray_fits_uint63 : forall n, (Z.of_nat ((to_nat n) * u64_bits) < wB)%Z.

(** Out-of-bounds set_bit is identity *)
Lemma set_bit_bounds : 
  forall {n : Uint63.int} (bits : BitArray n) idx value,
    Uint63.to_nat idx >= (to_nat n) * u64_bits ->
    set_bit bits idx value = bits.
Proof.
  intros n bits idx value H_bound.
  unfold set_bit.
  destruct (Uint63.to_nat idx <? (to_nat n) * u64_bits) eqn:H_lt.
  - rewrite Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

(** Setting a bit returns that value when read *)
Lemma get_bit_set_bit_same : 
  forall {n : Uint63.int} (bits : BitArray n) idx value,
    Uint63.to_nat idx < (to_nat n) * u64_bits ->
    get_bit (set_bit bits idx value) idx = value.
Proof.
  intros n bits idx value H_bound.
  unfold get_bit, set_bit.
  
  assert (H_lt: Uint63.to_nat idx <? (to_nat n) * u64_bits = true).
  { apply Nat.ltb_lt. exact H_bound. }
  
  rewrite H_lt.
  
  destruct value.
  - rewrite Z_to_bv_small.
    + rewrite Z.lor_spec.
      rewrite Z.shiftl_spec by apply (proj1 (to_Z_bounded idx)).
      replace (Uint63.to_Z idx - Uint63.to_Z idx)%Z with 0%Z by lia.
      simpl. rewrite Bool.orb_true_r. reflexivity.
    
    + split.
      * apply Z.lor_nonneg.
        -- split.
            ++ apply bv_unsigned_in_range.
            ++ apply Z.shiftl_nonneg. lia.
      * unfold bv_modulus.
        assert (H_bits_bound: (bv_unsigned bits < 2 ^ Z.of_nat ((to_nat n) * u64_bits))%Z).
        {
          pose proof (bv_unsigned_in_range (N.of_nat ((to_nat n) * u64_bits)) bits) as Hr.
          unfold bv_modulus in Hr.
          simpl in Hr.
          rewrite Z_of_N_of_nat in Hr.
          exact (proj2 Hr).
        }
        assert (H_shift_bound: (1 ≪ Uint63.to_Z idx < 2 ^ Z.of_nat ((to_nat n) * u64_bits))%Z).
        {
          rewrite Z.shiftl_1_l.
          apply Z.pow_lt_mono_r.
          - lia.
          - bv_solve. 
          - bv_solve.
          
        }
         assert (H_lor_bound: (Z.lor (bv_unsigned bits) (1 ≪ Uint63.to_Z idx) < 2 ^ Z.of_nat ((to_nat n) * u64_bits))%Z).
        {
          apply Z.bounded_iff_bits_nonneg.
          - lia.
          - apply Z.lor_nonneg.
            + split.
              * apply bv_unsigned_in_range.
              * apply Z.shiftl_nonneg. lia.
          - intros l Hl.
            rewrite Z.lor_spec.
            assert (H_bits_zero: Z.testbit (bv_unsigned bits) l = false).
            {
              apply bv_unsigned_spec_high.
              rewrite Z_of_N_of_nat.
              exact Hl.
            }
            assert (H_shift_zero: Z.testbit (1 ≪ Uint63.to_Z idx) l = false).
            {
              rewrite Z.shiftl_spec; [|lia].
              destruct (Z.eqb l (Uint63.to_Z idx)) eqn:Heq.
              - apply Z.eqb_eq in Heq. subst l.
                exfalso.
                apply Nat2Z.inj_lt in H_bound.
                lia.
              - assert (l - Uint63.to_Z idx ≠ 0)%Z.
                {
                  apply Z.eqb_neq in Heq.
                  intro Hcontra.
                  assert (l = Uint63.to_Z idx)%Z by lia.
                  contradiction.
                }
                destruct (Z.testbit 1 (l - Uint63.to_Z idx)) eqn:Hbit.
                --  exfalso.
                    assert (l - Uint63.to_Z idx = 0)%Z.
                    {
                      destruct (l - Uint63.to_Z idx)%Z eqn:Hd; try reflexivity.
                      - simpl in Hbit; discriminate.
                      - simpl in Hbit; discriminate.
                    }
                    contradiction.
                --  reflexivity.
            }
            rewrite H_bits_zero, H_shift_zero.
            reflexivity.
        }
        replace (Z.of_N (N.of_nat ((to_nat n) * u64_bits))) with (Z.of_nat ((to_nat n) * u64_bits)).
        -- exact H_lor_bound.
        -- bv_solve.
    
  - bv_simplify. 
    rewrite bv_wrap_spec_low.
    -- rewrite Z.land_spec.
      rewrite Z.lnot_spec; [|apply Uint63.to_Z_bounded].
      rewrite Z.shiftl_spec; [|apply to_Z_bounded].
      replace (to_Z idx - to_Z idx)%Z with 0%Z by lia.
      simpl.
      apply andb_false_r.
      
    -- split.
      + apply to_Z_bounded.
      + apply Nat2Z.inj_lt in H_bound.
        rewrite Z_of_N_of_nat.
        rewrite <- Nat2Z.inj_lt in H_bound.
        pose proof (to_Z_bounded idx) as [_ Hbound_z].
        assert (Z.of_nat (to_nat idx) = to_Z idx).
        {
          apply Z2Nat.id.
          apply to_Z_bounded.
        }
        rewrite <- H.
        apply Nat2Z.inj_lt.
        exact H_bound.  
Qed.

Lemma get_bit_set_bit_different : 
  forall {n : Uint63.int} (bits : BitArray n) (idx idx' : Uint63.int) value,
    Uint63.to_nat idx' < (to_nat n) * u64_bits ->
    idx <> idx' ->
    get_bit (set_bit bits idx value) idx' = get_bit bits idx'.
Proof.
  intros n bits idx idx' value H_bound H_neq.
  unfold get_bit, set_bit.
  
  destruct (Uint63.to_nat idx <? (to_nat n) * u64_bits) eqn:H_idx_bound.
  
  - assert (H_idx'_bound: Uint63.to_nat idx' <? (to_nat n) * u64_bits = true).
    { apply Nat.ltb_lt. assumption. }
    rewrite H_idx'_bound.
  
    destruct value.
  
    + rewrite Z_to_bv_small.
      * rewrite Z.lor_spec.
        assert (H_shift_bit: Z.testbit (Z.shiftl 1 (Uint63.to_Z idx)) (Uint63.to_Z idx') = false).
        { 
          rewrite Z.shiftl_spec; [|apply to_Z_bounded].
          destruct (Z.eqb (Uint63.to_Z idx') (Uint63.to_Z idx)) eqn:Heq.
          - apply Z.eqb_eq in Heq.
            assert (idx = idx') by (apply to_Z_inj; symmetry; exact Heq).
            contradiction H_neq.
          - assert (Uint63.to_Z idx' - Uint63.to_Z idx ≠ 0)%Z.
            {
              apply Z.eqb_neq in Heq.
              intro Hcontra.
              assert (Uint63.to_Z idx' = Uint63.to_Z idx)%Z by lia.
              contradiction.
            }
            destruct (Z.testbit 1 (Uint63.to_Z idx' - Uint63.to_Z idx)) eqn:Hbit.
            * exfalso.
              assert (Uint63.to_Z idx' - Uint63.to_Z idx = 0)%Z.
              {
                destruct (Uint63.to_Z idx' - Uint63.to_Z idx)%Z eqn:Hdiff; 
                try reflexivity; simpl in Hbit; discriminate.
              }
              contradiction.
            * reflexivity.
        }
        rewrite H_shift_bit.
        rewrite orb_false_r.
        reflexivity.
      * split.
        -- apply Z.lor_nonneg.
           split.
           ++ pose proof (bv_unsigned_in_range (N.of_nat ((to_nat n) * u64_bits)) bits) as Hr.
              exact (proj1 Hr).
           ++ apply Z.shiftl_nonneg; lia.
        -- unfold bv_modulus.
           rewrite Z_of_N_of_nat.
           apply Nat.ltb_lt in H_idx_bound.
           assert (H_bits_bound: (bv_unsigned bits < 2 ^ Z.of_nat ((to_nat n) * u64_bits))%Z).
           {
             pose proof (bv_unsigned_in_range (N.of_nat ((to_nat n) * u64_bits)) bits) as Hr.
             unfold bv_modulus in Hr.
             rewrite Z_of_N_of_nat in Hr.
             exact (proj2 Hr).
           }
           assert (H_shift_bound: (1 ≪ Uint63.to_Z idx < 2 ^ Z.of_nat ((to_nat n) * u64_bits))%Z).
           {
             rewrite Z.shiftl_1_l.
             apply Z.pow_lt_mono_r; try lia.
           }
             
           apply Nat2Z.inj_lt in H_idx_bound.
           apply Z.bounded_iff_bits_nonneg; try lia.
           apply Z.lor_nonneg; split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; lia].
           intros l Hl.
           rewrite Z.lor_spec.
           assert (H_bits_false: Z.testbit (bv_unsigned bits) l = false).
           {
             rewrite <- Z_of_N_of_nat in Hl.
             apply bv_unsigned_spec_high; exact Hl.
           }
           assert (H_shift_false: Z.testbit (1 ≪ Uint63.to_Z idx) l = false).
           {
             rewrite Z.shiftl_spec; [|lia].
             destruct (Z.eqb l (Uint63.to_Z idx)) eqn:Heq.
             - apply Z.eqb_eq in Heq. subst l.
               apply Nat2Z.inj_lt in H_idx_bound.
               assert (Z.of_nat (Uint63.to_nat idx) = Uint63.to_Z idx) by (apply Z2Nat.id; apply to_Z_bounded).
               lia.
             - destruct (Z.testbit 1 (l - Uint63.to_Z idx)) eqn:Hb; auto.
               exfalso.
               assert (l - Uint63.to_Z idx = 0)%Z by (destruct (l - Uint63.to_Z idx)%Z; auto; discriminate).
               apply Z.eqb_neq in Heq. lia.
           }
            rewrite H_bits_false, H_shift_false.
            reflexivity.
     + bv_simplify.
      rewrite bv_wrap_spec_low.
      * rewrite Z.land_spec, Z.lnot_spec; [|apply to_Z_bounded].
        assert (H_shift_bit: Z.testbit (Z.shiftl 1 (Uint63.to_Z idx)) (Uint63.to_Z idx') = false).
        { 
          rewrite Z.shiftl_spec; [|apply to_Z_bounded].
          destruct (Z.eqb (Uint63.to_Z idx') (Uint63.to_Z idx)) eqn:Heq.
          - apply Z.eqb_eq in Heq.
            assert (idx = idx') by (apply to_Z_inj; symmetry; exact Heq).
            contradiction H_neq.
          - assert (Uint63.to_Z idx' - Uint63.to_Z idx ≠ 0)%Z.
            {
              apply Z.eqb_neq in Heq.
              intro Hcontra.
              assert (Uint63.to_Z idx' = Uint63.to_Z idx)%Z by lia.
              contradiction.
            }
            destruct (Z.testbit 1 (Uint63.to_Z idx' - Uint63.to_Z idx)) eqn:Hbit.
            * exfalso.
              assert (Uint63.to_Z idx' - Uint63.to_Z idx = 0)%Z.
              {
                destruct (Uint63.to_Z idx' - Uint63.to_Z idx)%Z eqn:Hdiff; 
                try reflexivity; simpl in Hbit; discriminate.
              }
              contradiction.
            * reflexivity.
        }
        rewrite H_shift_bit.
        simpl.
        rewrite andb_true_r.
        reflexivity.
      * split.
        -- apply to_Z_bounded.
        -- bv_solve.
  
- assert (H_idx'_bound: Uint63.to_nat idx' <? (to_nat n) * u64_bits = true).
  { apply Nat.ltb_lt. assumption. }
    rewrite H_idx'_bound.
    reflexivity.
Qed.

Lemma first_one_returns_true : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    first_one_from_zero bits = Some idx -> 
    get_bit bits idx = true.
Proof.
  intros n bits idx H.
  unfold first_one_from_zero in H.
  destruct (find (fun i => Z.testbit (bv_unsigned bits) (Z.of_nat i)) (seq 0 ((to_nat n) * u64_bits))) as [i|] eqn:Hfind; [|discriminate].
  injection H as H. subst idx.
  
  apply find_some in Hfind.
  destruct Hfind as [Hin Hpred].
  apply in_seq in Hin.
  destruct Hin as [_ Hi_bound].
  
  unfold get_bit.
  
  assert (Hbound: Uint63.to_nat (of_Z (Z.of_nat i)) <? (to_nat n) * u64_bits = true).
  {
    apply Nat.ltb_lt.
    rewrite of_Z_spec, Zmod_small, Nat2Z.id; [exact Hi_bound | ].
    split; [lia | ].
    apply Nat2Z.inj_lt in Hi_bound.
    apply (Z.lt_trans _ (Z.of_nat ((to_nat n) * u64_bits)) _); [lia | ].
    apply bitarray_fits_uint63.
  }
  rewrite Hbound.
  
  assert (Heq: Uint63.to_Z (of_Z (Z.of_nat i)) = Z.of_nat i).
  {
    rewrite of_Z_spec, Zmod_small; [reflexivity | ].
    split; [lia | ].
    apply Nat2Z.inj_lt in Hi_bound.
    apply (Z.lt_trans _ (Z.of_nat ((to_nat n) * u64_bits)) _); [lia | ].
    apply bitarray_fits_uint63.
  }
  
  rewrite Heq.
  exact Hpred.
Qed.

(** Negation inverts each bit *)
Lemma bitnot_get_bit : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    Uint63.to_nat idx < (to_nat n) * u64_bits ->
    get_bit (bitnot bits) idx = negb (get_bit bits idx).
Proof.
  intros n bits idx H_bound.
  unfold bitnot, get_bit.
  
  assert (H_idx_lt: Uint63.to_nat idx <? (to_nat n) * u64_bits = true) by (apply Nat.ltb_lt; exact H_bound).
  rewrite H_idx_lt.
  
  rewrite bv_not_unsigned.
  
  rewrite bv_wrap_spec_low.
  - rewrite Z.lnot_spec.
    + reflexivity.
    + apply to_Z_bounded.
  - split.
    * apply to_Z_bounded.
    * rewrite Z_of_N_of_nat.
      rewrite <- (Z2Nat.id (to_Z idx)) by apply to_Z_bounded.
      apply Nat2Z.inj_lt.
      exact H_bound.
Qed.

(** Bitwise AND operates pointwise *)
Lemma bitand_get_bit : 
  forall {n : Uint63.int} (a b : BitArray n) idx,
    get_bit (bitand a b) idx = get_bit a idx && get_bit b idx.
Proof.
  intros n a b idx.
  unfold bitand, get_bit.
  
  destruct (Uint63.to_nat idx <? (to_nat n) * u64_bits) eqn:H_bound.
  - rewrite bv_and_unsigned.
    rewrite Z.land_spec.
    reflexivity.
    
  - reflexivity.
Qed.

Lemma count_ones_helper_monotonic :
  forall {n : Uint63.int} (bits : BitArray n) start remaining acc,
    count_ones_helper bits start remaining acc >= acc.
Proof.
  intros n bits start remaining acc.
  revert start acc.
  induction remaining as [|remaining' IH]; intros start acc.
  - simpl. lia.
  - simpl.
    destruct (Z.testbit (bv_unsigned bits) (Z.of_nat start)).
    + specialize (IH (S start) (S acc)).
      lia.
    + specialize (IH (S start) acc).
      exact IH.
Qed.

Lemma count_ones_helper_split :
  forall {n : Uint63.int} (bits : BitArray n) start1 len1 len2 acc,
    count_ones_helper bits start1 (len1 + len2) acc =
    count_ones_helper bits (start1 + len1) len2 
      (count_ones_helper bits start1 len1 acc).
Proof.
  intros n bits start1 len1.
  revert start1.
  induction len1 as [|len1' IH]; intros start1 len2 acc.
  - simpl. replace (start1 + 0) with start1 by lia. reflexivity.
  - simpl.
    replace (start1 + S len1') with (S (start1 + len1')) by lia.
    rewrite IH.
    reflexivity.
Qed.

Lemma count_ones_helper_bit_determines_count :
  forall {n : Uint63.int} (bits : BitArray n) start acc,
    start < (to_nat n) * u64_bits ->
    count_ones_helper bits start 1 acc = 
    if Z.testbit (bv_unsigned bits) (Z.of_nat start) then S acc else acc.
Proof.
  intros n bits start acc H_bound.
  simpl. reflexivity.
Qed.

Lemma count_ones_helper_extensional :
  forall {n : Uint63.int} (bits1 bits2 : BitArray n) start remaining acc,
    (forall i, start <= i < start + remaining -> 
       Z.testbit (bv_unsigned bits1) (Z.of_nat i) = 
       Z.testbit (bv_unsigned bits2) (Z.of_nat i)) ->
    count_ones_helper bits1 start remaining acc = 
    count_ones_helper bits2 start remaining acc.
Proof.
  intros n bits1 bits2 start remaining.
  revert start.
  induction remaining as [|remaining' IH]; intros start acc Hext.
  - reflexivity.
  - simpl.
    rewrite (Hext start); [|lia].
    destruct (Z.testbit (bv_unsigned bits2) (Z.of_nat start)); apply IH;
    intros i Hi; apply Hext; lia.
Qed.

(** Setting a bit different from current preserves other bits *)
Lemma get_bit_set_bit_diff : 
  forall {n : Uint63.int} (bits : BitArray n) idx1 idx2 value,
    idx1 <> idx2 ->
    get_bit (set_bit bits idx1 value) idx2 = get_bit bits idx2.
Proof.
  intros n bits idx1 idx2 value H_neq.
  destruct (Uint63.to_nat idx2 <? (to_nat n) * u64_bits) eqn:Hidx2.
  - apply Nat.ltb_lt in Hidx2.
    apply get_bit_set_bit_different; auto.
  - apply Nat.ltb_ge in Hidx2.
    rewrite get_bit_bounds; [|exact Hidx2].
    rewrite get_bit_bounds; [|exact Hidx2].
    reflexivity.
Qed.

Lemma count_ones_helper_zero_implies_all_false :
  forall {n : Uint63.int} (bits : BitArray n) start remaining acc,
    count_ones_helper bits start remaining acc = acc ->
    forall i, start <= i < start + remaining ->
    Z.testbit (bv_unsigned bits) (Z.of_nat i) = false.
Proof.
  intros n bits.
  intros start remaining.
  revert start.
  induction remaining as [|remaining' IH]; intros start acc Heq i Hrange.
  - simpl in Hrange. lia.
  - simpl in Heq.
    destruct (Nat.eq_dec i start) as [Hi_eq | Hi_neq].
    + subst i.
      destruct (Z.testbit (bv_unsigned bits) (Z.of_nat start)) eqn:Hbit.
      * exfalso.
        assert (Hgt: count_ones_helper bits (S start) remaining' (S acc) >= S acc).
        { apply count_ones_helper_monotonic. }
        lia.
      * reflexivity. 
        
    + assert (Hi_gt: start < i) by lia.
      assert (Hi_range': S start <= i < S start + remaining') by lia.
      
      destruct (Z.testbit (bv_unsigned bits) (Z.of_nat start)) eqn:Hstart.
      * exfalso.
        assert (Hgt: count_ones_helper bits (S start) remaining' (S acc) >= S acc).
        { apply count_ones_helper_monotonic. }
        lia.
      * apply (IH (S start) acc).
        -- exact Heq.
        -- exact Hi_range'.
Qed.

(** If count is 0, all bits are false *)
Lemma count_ones_zero_all_false : 
  forall {n : Uint63.int} (bits : BitArray n),
    count_ones bits = 0 -> forall idx, get_bit bits idx = false.
Proof.
  intros n bits Hcount idx.
  unfold get_bit.
  destruct (Uint63.to_nat idx <? (to_nat n) * u64_bits) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    unfold count_ones in Hcount.
    
    assert (H_eq: Z.testbit (bv_unsigned bits) (Z.of_nat (Uint63.to_nat idx)) = false).
    {
      apply count_ones_helper_zero_implies_all_false with (start := 0) (remaining := (to_nat n) * u64_bits) (acc := 0).
      + exact Hcount.
      + lia.
    }
    assert (H_simplify: Z.of_nat (Uint63.to_nat idx) = Uint63.to_Z idx).
    {
      apply Z2Nat.id.
      apply to_Z_bounded.
    }
    rewrite H_simplify in H_eq.
    exact H_eq.
    
  - reflexivity.
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.ZArith.Zbool.
Import ListNotations.
Require ZArith.

From stdpp Require Import bitvector.
From OC Require Import BitArr.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

(** * Helper Lemmas *)

(** Length of a list created by repeating an element n times equals n *)
Lemma eq_length_repeat {A : Type} (x : A) (n : nat) : length (repeat x n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** Out-of-bounds access returns false *)
Lemma get_bit_bounds : 
  forall {n : nat} (bits : BitArray n) idx,
    idx >= n * u64_bits ->
    get_bit bits idx = false.
Proof.
  intros n bits idx H_bound.
  unfold get_bit.
  destruct (idx <? n * u64_bits) eqn:H_lt.
  - rewrite Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

(** Out-of-bounds set_bit is identity *)
Lemma set_bit_bounds : 
  forall {n : nat} (bits : BitArray n) idx value,
    idx >= n * u64_bits ->
    set_bit bits idx value = bits.
Proof.
  intros n bits idx value H_bound.
  unfold set_bit.
  destruct (idx <? n * u64_bits) eqn:H_lt.
  - rewrite Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

Search bv_unsigned Z_to_bv.
(** Setting a bit returns that value when read *)
Lemma get_bit_set_bit_same : 
  forall {n : nat} (bits : BitArray n) idx value,
    idx < n * u64_bits ->
    get_bit (set_bit bits idx value) idx = value.
Proof.
  intros n bits idx value H_bound.
  unfold get_bit, set_bit.
  
  assert (H_lt: idx <? n * u64_bits = true).
  { apply Nat.ltb_lt. exact H_bound. }
  
  rewrite H_lt.
  
  destruct value.
  - rewrite Z_to_bv_small.
    + rewrite Z.lor_spec.
      rewrite Z.shiftl_spec.
      * replace (Z.of_nat idx - Z.of_nat idx)%Z with 0%Z by lia.
        simpl. rewrite Bool.orb_true_r. reflexivity.
      * lia.
    
    + split.
      * apply Z.lor_nonneg.
        -- split.
            ++ apply bv_unsigned_in_range.
            ++ apply Z.shiftl_nonneg. lia.
      * unfold bv_modulus.
        assert (H_bits_bound: (bv_unsigned bits < 2 ^ Z.of_nat (n * u64_bits))%Z).
        {
          pose proof (bv_unsigned_in_range (N.of_nat (n * u64_bits)) bits) as Hr.
          unfold bv_modulus in Hr.
          simpl in Hr.
          rewrite Z_of_N_of_nat in Hr.
          exact (proj2 Hr).
        }
        assert (H_shift_bound: (1 ≪ Z.of_nat idx < 2 ^ Z.of_nat (n * u64_bits))%Z).
        {
          rewrite Z.shiftl_1_l.
          apply Z.pow_lt_mono_r.
          - lia.
          - bv_solve. 
          - bv_solve. 
          
        }
         assert (H_lor_bound: (Z.lor (bv_unsigned bits) (1 ≪ Z.of_nat idx) < 2 ^ Z.of_nat (n * u64_bits))%Z).
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
            assert (H_shift_zero: Z.testbit (1 ≪ Z.of_nat idx) l = false).
            {
              rewrite Z.shiftl_spec; [|lia].
              destruct (Z.eqb l (Z.of_nat idx)) eqn:Heq.
              - apply Z.eqb_eq in Heq. subst l.
                exfalso.
                apply Nat2Z.inj_lt in H_bound.
                lia.
              - assert (l - Z.of_nat idx ≠ 0)%Z.
                {
                  apply Z.eqb_neq in Heq.
                  intro Hcontra.
                  assert (l = Z.of_nat idx)%Z by lia.
                  contradiction.
                }
                destruct (Z.testbit 1 (l - Z.of_nat idx)) eqn:Hbit.
                --  exfalso.
                    assert (l - Z.of_nat idx = 0)%Z.
                    {
                      destruct (l - Z.of_nat idx)%Z eqn:Hd; try reflexivity.
                      - simpl in Hbit; discriminate.
                      - simpl in Hbit; discriminate.
                    }
                    contradiction.
                --  reflexivity.
            }
            rewrite H_bits_zero, H_shift_zero.
            reflexivity.
        }
        replace (Z.of_N (N.of_nat (n * u64_bits))) with (Z.of_nat (n * u64_bits)).
        -- exact H_lor_bound.
        -- bv_solve.
    
  - bv_simplify. 
    rewrite bv_wrap_spec_low.
    -- rewrite Z.land_spec, Z.lnot_spec by lia.
      rewrite Z.shiftl_spec by lia.
      replace (Z.sub (Z.of_nat idx) (Z.of_nat idx)) with 0%Z by lia.
      simpl Z.testbit.
      rewrite andb_false_r.
      reflexivity.
    -- split.
      + lia.
      + apply Nat2Z.inj_lt in H_bound.
        rewrite Z_of_N_of_nat.
        exact H_bound.
Qed.

Search Z"lor".
Search "lor" bv.

Lemma get_bit_set_bit_different : 
  forall {n : nat} (bits : BitArray n) idx idx' value,
    idx' < n * u64_bits ->
    idx <> idx' ->
    get_bit (set_bit bits idx value) idx' = get_bit bits idx'.
Proof.
  Admitted.

Lemma first_one_returns_true : 
  forall {n : nat} (bits : BitArray n) idx,
    first_one_from_zero bits = Some idx -> 
    get_bit bits idx = true.
Proof.
Admitted.

Search Z.testbit "shiftl".
(** Setting a bit different from current preserves other bits *)
Lemma get_bit_set_bit_diff : 
  forall {n : nat} (bits : BitArray n) idx1 idx2 value,
    idx1 <> idx2 ->
    get_bit (set_bit bits idx1 value) idx2 = get_bit bits idx2.
Proof.
  intros n bits idx1 idx2 value H_neq.
  unfold get_bit, set_bit.
  
  admit.
Admitted.

(** Negation inverts each bit *)
Lemma bitnot_get_bit : 
  forall {n : nat} (bits : BitArray n) idx,
    idx < n * u64_bits ->
    get_bit (bitnot bits) idx = negb (get_bit bits idx).
Proof.
  intros n bits idx H_bound.
  unfold bitnot, get_bit.
  
  admit.
Admitted.

(** Bitwise AND operates pointwise *)
Lemma bitand_get_bit : 
  forall {n : nat} (a b : BitArray n) idx,
    get_bit (bitand a b) idx = get_bit a idx && get_bit b idx.
Proof.
  intros n a b idx.
  unfold bitand, get_bit.
  
  admit.
Admitted.

(** Setting a bit to true increases the count of ones exactly by 1 *)
Lemma set_bit_false_to_true_increases_count : 
  forall {n : nat} (bits : BitArray n) (idx : nat),
    idx < n * u64_bits ->
    get_bit bits idx = false ->
    count_ones (set_bit bits idx true) = count_ones bits + 1.
Proof.
  intros n bits idx H_bound H_false.
  unfold count_ones, set_bit, get_bit in *.
  
Admitted.

(** If count is 0, all bits are false *)
Lemma count_ones_zero_all_false : 
  forall {n : nat} (bits : BitArray n),
    count_ones bits = 0 -> forall idx, get_bit bits idx = false.
Proof.
  intros n bits H_zero idx.
  unfold count_ones, get_bit in *.
  
Admitted.

(** Setting a bit to false decreases the count of ones exactly by 1 *)
Lemma set_bit_true_to_false_decreases_count : 
  forall {n : nat} (bits : BitArray n) (idx : nat),
    idx < n * u64_bits ->
    get_bit bits idx = true ->
    count_ones (set_bit bits idx false) = count_ones bits - 1.
Proof.
  intros n bits idx H_bound H_true.
  unfold count_ones, set_bit, get_bit in *.
  
Admitted.
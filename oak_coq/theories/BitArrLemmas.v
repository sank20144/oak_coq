Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

From stdpp Require Import bitvector.
From OC Require Import BitArr.

(** * Helper Lemmas *)

(** Length of a list created by repeating an element n times equals n *)
Lemma eq_length_repeat {A : Type} (x : A) (n : nat) : length (repeat x n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** Out-of-bounds access returns false *)
Lemma get_bit_bounds : 
  forall {n : nat} (bits : BitArray n) idx,
    idx >= n ->
    get_bit bits idx = false.
Proof.
  intros n bits idx H_bound.
  unfold get_bit.
  destruct (idx <? n) eqn:H_lt.
  - rewrite Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

(** Out-of-bounds set_bit is identity *)
Lemma set_bit_bounds : 
  forall {n : nat} (bits : BitArray n) idx value,
    idx >= n ->
    set_bit bits idx value = bits.
Proof.
  intros n bits idx value H_bound.
  unfold set_bit.
  destruct (idx <? n) eqn:H_lt.
  - rewrite Nat.ltb_lt in H_lt. lia.
  - reflexivity.
Qed.

(** Setting a bit returns that value when read *)
Lemma get_bit_set_bit_same : 
  forall {n : nat} (bits : BitArray n) idx value,
    idx < n ->
    get_bit (set_bit bits idx value) idx = value.
Proof.
  intros n bits idx value H_bound.
  unfold get_bit, set_bit.
  assert (H_lt: idx <? n = true) by (apply Nat.ltb_lt; exact H_bound).
  rewrite H_lt.
  destruct value.
  - admit.
  - admit.
Admitted.

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
    idx < n ->
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
    idx < n ->
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
    idx < n ->
    get_bit bits idx = true ->
    count_ones (set_bit bits idx false) = count_ones bits - 1.
Proof.
  intros n bits idx H_bound H_true.
  unfold count_ones, set_bit, get_bit in *.
  
Admitted.
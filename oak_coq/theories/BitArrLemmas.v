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
Admitted.

Lemma get_bit_bounds : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    Uint63.to_nat idx >= (to_nat n) * u64_bits ->
    get_bit bits idx = false.
Proof.
Admitted.

(** Out-of-bounds set_bit is identity *)
Lemma set_bit_bounds : 
  forall {n : Uint63.int} (bits : BitArray n) idx value,
    Uint63.to_nat idx >= (to_nat n) * u64_bits ->
    set_bit bits idx value = bits.
Proof.
Admitted.

(** Setting a bit returns that value when read *)
Lemma get_bit_set_bit_same : 
  forall {n : Uint63.int} (bits : BitArray n) idx value,
    Uint63.to_nat idx < (to_nat n) * u64_bits ->
    get_bit (set_bit bits idx value) idx = value.
Proof.
Admitted.

Lemma get_bit_set_bit_different : 
  forall {n : Uint63.int} (bits : BitArray n) (idx idx' : Uint63.int) value,
    Uint63.to_nat idx' < (to_nat n) * u64_bits ->
    idx <> idx' ->
    get_bit (set_bit bits idx value) idx' = get_bit bits idx'.
Proof.
Admitted.

Lemma first_one_returns_true : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    (Z.of_nat ((to_nat n) * u64_bits) < wB)%Z ->
    first_one_from_zero bits = Some idx -> 
    get_bit bits idx = true.
Proof.
Admitted.

(** Negation inverts each bit *)
Lemma bitnot_get_bit : 
  forall {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int),
    Uint63.to_nat idx < (to_nat n) * u64_bits ->
    get_bit (bitnot bits) idx = negb (get_bit bits idx).
Proof.
Admitted.

(** Bitwise AND operates pointwise *)
Lemma bitand_get_bit : 
  forall {n : Uint63.int} (a b : BitArray n) idx,
    get_bit (bitand a b) idx = get_bit a idx && get_bit b idx.
Proof.
Admitted.

Lemma count_ones_helper_monotonic :
  forall {n : Uint63.int} (bits : BitArray n) start remaining acc,
    count_ones_helper bits start remaining acc >= acc.
Proof.
Admitted.

Lemma count_ones_helper_split :
  forall {n : Uint63.int} (bits : BitArray n) start1 len1 len2 acc,
    count_ones_helper bits start1 (len1 + len2) acc =
    count_ones_helper bits (start1 + len1) len2 
      (count_ones_helper bits start1 len1 acc).
Proof.
Admitted.

Lemma count_ones_helper_bit_determines_count :
  forall {n : Uint63.int} (bits : BitArray n) start acc,
    start < (to_nat n) * u64_bits ->
    count_ones_helper bits start 1 acc = 
    if Z.testbit (bv_unsigned bits) (Z.of_nat start) then S acc else acc.
Proof.
Admitted.

Lemma count_ones_helper_extensional :
  forall {n : Uint63.int} (bits1 bits2 : BitArray n) start remaining acc,
    (forall i, start <= i < start + remaining -> 
       Z.testbit (bv_unsigned bits1) (Z.of_nat i) = 
       Z.testbit (bv_unsigned bits2) (Z.of_nat i)) ->
    count_ones_helper bits1 start remaining acc = 
    count_ones_helper bits2 start remaining acc.
Proof.
Admitted.

(** Setting a bit different from current preserves other bits *)
Lemma get_bit_set_bit_diff : 
  forall {n : Uint63.int} (bits : BitArray n) idx1 idx2 value,
    idx1 <> idx2 ->
    get_bit (set_bit bits idx1 value) idx2 = get_bit bits idx2.
Proof.
Admitted.

Lemma count_ones_helper_zero_implies_all_false :
  forall {n : Uint63.int} (bits : BitArray n) start remaining acc,
    count_ones_helper bits start remaining acc = acc ->
    forall i, start <= i < start + remaining ->
    Z.testbit (bv_unsigned bits) (Z.of_nat i) = false.
Proof.
Admitted.

(** If count is 0, all bits are false *)
Lemma count_ones_zero_all_false : 
  forall {n : Uint63.int} (bits : BitArray n),
    count_ones bits = 0 -> forall idx, get_bit bits idx = false.
Proof.
Admitted.

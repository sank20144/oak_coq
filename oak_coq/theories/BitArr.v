Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

From stdpp Require Import bitvector.

(** * Bitmap representation *)

Definition u64_bits : nat := 64.

Definition BitArray (n : nat) := bv (N.of_nat (n * u64_bits)).

(** Get value from bitmap at index *)
Definition get_bit {n : nat} (bits : BitArray n) (idx : nat) : bool :=
  let total_bits := n * u64_bits in
  if idx <? total_bits then
    Z.testbit (bv_unsigned bits) (Z.of_nat idx)
  else false.

(** Set value in bitmap at index *)
Definition set_bit {n : nat} (bits : BitArray n) (idx : nat) (value : bool) : BitArray n :=
  let total_bits := n * u64_bits in
  if idx <? total_bits then
    let current_val := bv_unsigned bits in
    let new_val := if value then
      Z.lor current_val (Z.shiftl 1 (Z.of_nat idx))
    else
      Z.land current_val (Z.lnot (Z.shiftl 1 (Z.of_nat idx))) in
    Z_to_bv (N.of_nat total_bits) new_val
  else bits.

(** Perform logical AND between two bitmaps *)
Definition bitand {n : nat} (a b : BitArray n) : BitArray n :=
  bv_and a b.

(** Perform logical NOT on a bitmap *)
Definition bitnot {n : nat} (a : BitArray n) : BitArray n :=
  bv_not a.

(** Find index of first 1 bit *)
Fixpoint first_one_fuel {n : nat} (bits : BitArray n) (start_idx : nat) (fuel : nat) : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
    let total_bits := n * u64_bits in
    if start_idx <? total_bits then
      if Z.testbit (bv_unsigned bits) (Z.of_nat start_idx) then
        Some start_idx
      else
        first_one_fuel bits (S start_idx) fuel'
    else None
  end.

Definition first_one {n : nat} (bits : BitArray n) (start_idx : nat) : option nat :=
  let total_bits := n * u64_bits in
  first_one_fuel bits start_idx (total_bits - start_idx).

Definition first_one_from_zero {n : nat} (bits : BitArray n) : option nat :=
  first_one bits 0.

(** Count number of ones in a bitmap *)
Fixpoint count_ones_helper {n : nat} (bits : BitArray n) (fuel : nat) (i : nat) (acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    let total_bits := n * u64_bits in
    if i <? total_bits then
      let new_acc := if Z.testbit (bv_unsigned bits) (Z.of_nat i) then S acc else acc in
      count_ones_helper bits fuel' (S i) new_acc
    else acc
  end.

Definition count_ones {n : nat} (bits : BitArray n) : nat :=
  let total_bits := n * u64_bits in
  count_ones_helper bits total_bits 0 0.

(** Create zero-initialized BitArray *)
Definition make_bitarray (n : nat) : BitArray n :=
  Z_to_bv (N.of_nat (n * u64_bits)) 0.

Fixpoint bits_to_z_helper (bits : list bool) (pos : nat) (acc : Z) : Z :=
  match bits with
  | [] => acc
  | b :: bs => 
      let new_acc := if b then Z.lor acc (Z.shiftl 1 (Z.of_nat pos)) else acc in
      bits_to_z_helper bs (S pos) new_acc
  end.

(** Create BitArray from list bool - note: list length should be multiple of 64 *)
Definition bitarray_from_list (bits : list bool) : BitArray (Nat.div (length bits) u64_bits) :=
  let n := Nat.div (length bits) u64_bits in
  Z_to_bv (N.of_nat (n * u64_bits)) (bits_to_z_helper bits 0 0).

(** Convert BitArray to list bool *)
Fixpoint z_to_bits_helper (fuel : nat) (total_bits : nat) (i : nat) (z : Z) (acc : list bool) : list bool :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    if i <? total_bits then
      let bit := Z.testbit z (Z.of_nat (total_bits - 1 - i)) in
      z_to_bits_helper fuel' total_bits (S i) z (bit :: acc)
    else acc
  end.

Definition bitarray_to_list {n : nat} (bits : BitArray n) : list bool :=
  let total_bits := n * u64_bits in
  z_to_bits_helper total_bits total_bits 0 (bv_unsigned bits) [].

(** Helper to get total bit capacity *)
Definition bitarray_capacity (n : nat) : nat := n * u64_bits.

Compute (bitarray_capacity 4096). (* Should be 262144 bits *)
Compute (make_bitarray 4096).
Compute set_bit (make_bitarray 10) 65 true. (* Setting bit 65 (second u64, second bit) *)
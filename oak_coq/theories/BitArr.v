Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

From stdpp Require Import bitvector.

(** * Bitmap representation *)

Definition BitArray (n : nat) := bv (N.of_nat n).

(** Get value from bitmap at index *)
Definition get_bit {n : nat} (bits : BitArray n) (idx : nat) : bool :=
  if idx <? n then
    Z.testbit (bv_unsigned bits) (Z.of_nat idx)
  else false.

(** Set value in bitmap at index *)
Definition set_bit {n : nat} (bits : BitArray n) (idx : nat) (value : bool) : BitArray n :=
  if idx <? n then
    let current_val := bv_unsigned bits in
    let new_val := if value then
      Z.lor current_val (Z.shiftl 1 (Z.of_nat idx))
    else
      Z.land current_val (Z.lnot (Z.shiftl 1 (Z.of_nat idx))) in
    Z_to_bv (N.of_nat n) new_val
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
    if start_idx <? n then
      if Z.testbit (bv_unsigned bits) (Z.of_nat start_idx) then
        Some start_idx
      else
        first_one_fuel bits (S start_idx) fuel'
    else None
  end.

Definition first_one {n : nat} (bits : BitArray n) (start_idx : nat) : option nat :=
  first_one_fuel bits start_idx (n - start_idx).

Definition first_one_from_zero {n : nat} (bits : BitArray n) : option nat :=
  first_one bits 0.

(** Count number of ones in a bitmap *)
Fixpoint count_ones_helper {n : nat} (bits : BitArray n) (fuel : nat) (i : nat) (acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    if i <? n then
      let new_acc := if Z.testbit (bv_unsigned bits) (Z.of_nat i) then S acc else acc in
      count_ones_helper bits fuel' (S i) new_acc
    else acc
  end.

Definition count_ones {n : nat} (bits : BitArray n) : nat :=
  count_ones_helper bits n 0 0.


(** Create zero-initialized BitArray *)
Definition make_bitarray (n : nat) : BitArray n :=
  Z_to_bv (N.of_nat n) 0.

Fixpoint bits_to_z_helper (bits : list bool) (pos : nat) (acc : Z) : Z :=
  match bits with
  | [] => acc
  | b :: bs => 
      let new_acc := if b then Z.lor acc (Z.shiftl 1 (Z.of_nat pos)) else acc in
      bits_to_z_helper bs (S pos) new_acc
  end.

(** Create BitArray from list bool *)
Definition bitarray_from_list (bits : list bool) : BitArray (length bits) :=
  let n := length bits in
  Z_to_bv (N.of_nat n) (bits_to_z_helper bits 0 0).

(** Convert BitArray to list bool *)
Fixpoint z_to_bits_helper (fuel : nat) (n : nat) (i : nat) (z : Z) (acc : list bool) : list bool :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    if i <? n then
      let bit := Z.testbit z (Z.of_nat (n - 1 - i)) in
      z_to_bits_helper fuel' n (S i) z (bit :: acc)
    else acc
  end.

Definition bitarray_to_list {n : nat} (bits : BitArray n) : list bool :=
  z_to_bits_helper n n 0 (bv_unsigned bits) [].


Compute (make_bitarray 5).
Compute set_bit (make_bitarray 5) 1 true.

Compute bitarray_to_list (set_bit (make_bitarray 15) 6 true ).
Compute bitarray_to_list (bitarray_from_list [true; false; true; false; true]).

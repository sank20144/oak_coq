Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.

From stdpp Require Import bitvector.

(** * Bitmap representation *)

Definition u64_bits : nat := 64.

Definition BitArray (n : Uint63.int) := bv (N.of_nat ((to_nat n) * u64_bits)).

(** Get value from bitmap at index *)
Definition get_bit {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) : bool :=
  let total_bits := (to_nat n) * u64_bits in
  if (Uint63.to_nat idx) <? total_bits then
    Z.testbit (bv_unsigned bits) (Uint63.to_Z idx)
  else false.

(** Set value in bitmap at index **)
Definition set_bit {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) (value : bool) : BitArray n :=
  let total_bits := (to_nat n) * u64_bits in
  if (Uint63.to_nat idx) <? total_bits then
    let current_val := bv_unsigned bits in
    let new_val := if value then
      Z.lor current_val (Z.shiftl 1 (Uint63.to_Z idx))
    else
      Z.land current_val (Z.lnot (Z.shiftl 1 (Uint63.to_Z idx))) in
    Z_to_bv (N.of_nat total_bits) new_val
  else bits.

(** Perform logical AND between two bitmaps *)
Definition bitand {n : Uint63.int} (a b : BitArray n) : BitArray n :=
  bv_and a b.

(** Perform logical NOT on a bitmap *)
Definition bitnot {n : Uint63.int} (a : BitArray n) : BitArray n :=
  bv_not a.

(** Find index of first 1 bit *)
Definition first_one_from_zero {n : Uint63.int} (bits : BitArray n) : option Uint63.int :=
  let total_bits := (to_nat n) * u64_bits in
  option_map (fun i => Uint63.of_Z (Z.of_nat i)) (find (fun i => Z.testbit (bv_unsigned bits) (Z.of_nat i)) (seq 0 total_bits)).

(** Count number of ones in a bitmap *)
Fixpoint count_ones_helper {n : Uint63.int} (bits : BitArray n) (i : nat) (remaining : nat) (acc : nat) : nat :=
  match remaining with
  | 0 => acc
  | S remaining' =>
    let new_acc := if Z.testbit (bv_unsigned bits) (Z.of_nat i) then S acc else acc in
    count_ones_helper bits (S i) remaining' new_acc
  end.

Definition count_ones {n : Uint63.int} (bits : BitArray n) : nat :=
  let total_bits := (to_nat n) * u64_bits in
  count_ones_helper bits 0 total_bits 0.

(** Create zero-initialized BitArray *)
Definition make_bitarray (n : Uint63.int) : BitArray n :=
  Z_to_bv (N.of_nat ((to_nat n) * u64_bits)) 0.

Fixpoint bits_to_z_helper (bits : list bool) (pos : nat) (acc : Z) : Z :=
  match bits with
  | [] => acc
  | b :: bs => 
      let new_acc := if b then Z.lor acc (Z.shiftl 1 (Z.of_nat pos)) else acc in
      bits_to_z_helper bs (S pos) new_acc
  end.

(** Create BitArray from list bool - note: list length should be multiple of 64 *)
Definition bitarray_from_list (bits : list bool) : option { n : Uint63.int & BitArray n } :=
  if Nat.modulo (length bits) u64_bits =? 0 then
    let n_nat := Nat.div (length bits) u64_bits in
    let n := Uint63.of_Z (Z.of_nat n_nat) in
    Some (existT n (Z_to_bv (N.of_nat (to_nat n * u64_bits)) (bits_to_z_helper bits 0 0)))
  else None.

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

Definition bitarray_to_list {n : Uint63.int} (bits : BitArray n) : list bool :=
  let total_bits := (to_nat n) * u64_bits in
  z_to_bits_helper total_bits total_bits 0 (bv_unsigned bits) [].

(** Helper to get total bit capacity *)
Definition bitarray_capacity (n : Uint63.int) : nat := (to_nat n) * u64_bits.

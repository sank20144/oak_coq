Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Eqdep_dec.
Import ListNotations.
From stdpp Require Import bitvector.
From OC Require Import BitArr.
From OC Require Import VariableModel.
From OC Require Import PhysicalMemory.
From OC Require Import BitmapAllocatorCore.
From OC Require Import BitArrLemmas.

Local Open Scope string_scope.
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

(** Helper lemma: first_one_from_zero returns indices within bounds *)
Lemma first_one_from_zero_lt {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) :
  first_one_from_zero bits = Some idx ->
  Uint63.to_nat idx < to_nat n * u64_bits.
Proof.
  intros H.
  unfold first_one_from_zero in H.
  destruct (find (fun i => Z.testbit (bv_unsigned bits) (Z.of_nat i)) (seq 0 (to_nat n * u64_bits))) as [i|] eqn:Hfind.
  - injection H as H. subst idx.
    apply find_some in Hfind.
    destruct Hfind as [Hin _].
    apply in_seq in Hin.
    destruct Hin as [_ Hi_bound].
    rewrite of_Z_spec.
    rewrite Zmod_small.
    + rewrite Nat2Z.id. exact Hi_bound.
    + split.
      * lia.
      * apply Nat2Z.inj_lt in Hi_bound.
        apply (Z.lt_trans _ (Z.of_nat (to_nat n * u64_bits)) _).
        -- exact Hi_bound.
        -- apply bitarray_fits_uint63.
  - discriminate H.
Qed.

Lemma first_one_some_implies_nonzero_count {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) :
  first_one_from_zero bits = Some idx ->
  count_ones bits > 0.
Proof.
  intros H.
  assert (H_bit_true: get_bit bits idx = true).
  { apply first_one_returns_true; exact H. }
  
  assert (H_idx_bound: Uint63.to_nat idx < to_nat n * u64_bits).
  { apply (first_one_from_zero_lt bits); exact H. }

  destruct (count_ones bits) eqn:Hcount.
  - pose proof (count_ones_zero_all_false bits Hcount idx) as H_bit_false.
    rewrite H_bit_true in H_bit_false.
    discriminate.
  - lia.
Qed.


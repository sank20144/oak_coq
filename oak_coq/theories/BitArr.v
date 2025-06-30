Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(** * Bitmap representation *)

Definition BitArray := list bool.

(** * Helper Lemmas *)

(** Length of a list created by repeating an element n times equals n *)
Lemma eq_length_repeat {A : Type} (x : A) (n : nat) : length (repeat x n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** * Utility Functions *)

(** Get value from bitmap at index *)
Definition get_bit (bits : BitArray) (idx : nat) : bool :=
  nth idx bits false.

(** Set value in bitmap at index *)
Fixpoint set_bit (bits : BitArray) (idx : nat) (value : bool) : BitArray :=
  match bits, idx with
  | [], _ => []
  | b :: bs, 0 => value :: bs
  | b :: bs, S n => b :: set_bit bs n value
  end.

(** Perform logical AND between two bitmaps *)
Definition bitand (a : BitArray) (b : BitArray) : BitArray :=
  map (fun '(x, y) => andb x y) (combine a b).

(** Perform logical NOT on a bitmap *)
Definition bitnot (a : BitArray) : BitArray :=
  map negb a.

(** Find index of first 1 bit *)
Fixpoint first_one (bits : BitArray) (start_idx : nat) : option nat :=
  match bits with
  | [] => None
  | true :: _ => Some start_idx
  | false :: bs => first_one bs (S start_idx)
  end.

Definition first_one_from_zero (bits : BitArray) : option nat :=
  first_one bits 0.

(** Count number of ones in a bitmap *)
Fixpoint count_ones (bits : BitArray) : nat :=
  match bits with
  | [] => 0
  | true :: bs => S (count_ones bs)
  | false :: bs => count_ones bs
  end.

(** * BitArray Lemmas *)

Lemma set_bit_preserves_length : 
forall (bits : list bool) (i : nat) (b : bool),
  length (set_bit bits i b) = length bits.
Proof.
  intros bits i b.
  generalize dependent i.
  induction bits as [|h t IH]; intros i.
  - destruct i; simpl; reflexivity.
  - destruct i as [|i'].
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

Lemma get_bit_correct :
  forall (bits : BitArray) (idx : nat),
    idx < length bits ->
    get_bit bits idx = nth idx bits false.
Proof.
  intros.
  induction bits as [|b bs IH]; intros.
  - simpl in *. lia.
  - destruct idx as [|idx'].
    + simpl. reflexivity.
    + simpl in *. 
      unfold get_bit in *.
      simpl. reflexivity.
Qed.

(** Lemma: setting a bit to true increases the count of ones exactly by 1 *)
Lemma set_bit_false_to_true_increases_count : 
  forall (bits : BitArray) (idx : nat),
    idx < length bits ->
    get_bit bits idx = false ->
    count_ones (set_bit bits idx true) = count_ones bits + 1.
Proof.
  intros bits idx H_len H_false.
  generalize dependent idx.
  induction bits as [|b bs IH]; intros idx H_len H_false.
  - simpl in *. lia.
  - destruct idx as [|idx'].
    + simpl in *. 
      destruct b.
      -- simpl. discriminate H_false.
      -- simpl. rewrite Nat.add_1_r. reflexivity.
    + simpl in *. 
      destruct b; simpl.
      -- f_equal. apply IH. lia. assumption.
      -- simpl in *. rewrite IH; auto. lia.
Qed.

(* if count_ones is 0, then all bits are false *)
Lemma count_ones_zero_all_false : forall (bits : BitArray),
  count_ones bits = 0 -> forall idx, get_bit bits idx = false.
Proof.
  intros bits H_zero idx.
  generalize dependent idx.
  unfold get_bit.
  induction bits as [|b bs IH].
  - destruct idx; simpl; reflexivity.
  - simpl in H_zero.
    destruct b.
    + simpl in H_zero. discriminate H_zero.
    + destruct idx as [|idx'].
      * simpl. reflexivity.
      * simpl in *. apply IH. assumption.
Qed.

Lemma set_bit_true_to_false_decreases_count : 
  forall (bits : BitArray) (idx : nat),
    idx < length bits ->
    get_bit bits idx = true ->
    count_ones (set_bit bits idx false) = count_ones bits - 1.
Proof.
  intros bits idx H_len H_true.
  generalize dependent idx.
  induction bits as [|b bs IH]; intros idx H_len H_true.
  - simpl in *. lia.
  - destruct idx as [|idx'].
    + simpl in *. 
      destruct b.
      -- simpl. lia.
      -- simpl in H_true. discriminate H_true.
    + simpl in *. 
      destruct b; simpl.
      -- rewrite IH.
         * assert (H_bs_true: get_bit bs idx' = true).
           { simpl in H_true. assumption. }
           assert (H_count_pos: count_ones bs > 0).
           { 
             destruct (count_ones bs) eqn:H_count.
             - pose proof (count_ones_zero_all_false bs H_count idx') as H_false.
               rewrite H_false in H_bs_true.
               discriminate H_bs_true.
             - lia.
           }
           lia.
         * lia.
         * assumption.
      -- rewrite IH.
         * lia.
         * lia. 
         * assumption.
Qed.

Lemma get_bit_set_bit_same : forall (bits : BitArray) idx value,
  idx < length bits ->
  get_bit (set_bit bits idx value) idx = value.
Proof.
  intros bits idx value H_bound.
  generalize dependent idx.
  induction bits as [|b bs IH]; intros idx H_bound.
  - simpl in *. lia.
  - destruct idx as [|idx'].
    + simpl. reflexivity.
    + simpl. unfold get_bit.
      simpl. apply IH.
      simpl in *.
      lia.
Qed.

Lemma length_bitnot : forall (bits : BitArray),
  length (bitnot bits) = length bits.
Proof.
  intro bits.
  unfold bitnot.
  apply length_map.
Qed.

Lemma nth_map_negb : forall (l : list bool) (n : nat),
  nth n (map negb l) false = 
  if n <? length l then negb (nth n l false) else false.
Proof.
  intros l n.
  generalize dependent n.
  induction l as [|a l' IH]; intros n.
  - simpl. destruct n; reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. 
      apply IH.
Qed.

Lemma bitnot_get_bit : forall (bits : BitArray) idx,
  idx < length bits ->
  get_bit (bitnot bits) idx = negb (get_bit bits idx).
Proof.
  intros bits idx H_bound.
  unfold bitnot, get_bit.
  rewrite nth_map_negb.
  rewrite <- Nat.ltb_lt in H_bound.
  rewrite H_bound.
  reflexivity.
Qed.

Lemma nth_combine_default : forall {A B : Type} (l1 : list A) (l2 : list B) (n : nat) (d1 : A) (d2 : B),
  length l1 = length l2 ->
  nth n (combine l1 l2) (d1, d2) = (nth n l1 d1, nth n l2 d2).
Proof.
  intros A B l1 l2 n d1 d2 H_eq.
  generalize dependent l2.
  generalize dependent n.
  induction l1 as [|a1 l1' IH]; intros n l2 H_eq.
  - destruct l2; [|discriminate H_eq].
    destruct n; simpl; reflexivity.
  - destruct l2 as [|a2 l2']; [discriminate H_eq|].
    destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. apply IH.
      simpl in H_eq. injection H_eq. auto.
Qed.

(** Helper lemma about nth and map with andb function *)
Lemma nth_map_andb : forall (l : list (bool * bool)) (n : nat),
  nth n (map (fun '(x, y) => andb x y) l) false = 
  let '(x, y) := nth n l (false, false) in andb x y.
Proof.
  intros l n.
  generalize dependent n.
  induction l as [|[a b] l' IH]; intros n.
  - destruct n; simpl; reflexivity.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.

Lemma bitand_get_bit : forall (a b : BitArray) idx,
  length a = length b ->
  get_bit (bitand a b) idx = get_bit a idx && get_bit b idx.
Proof.
  intros a b idx H_eq.
  unfold bitand, get_bit.
  rewrite nth_map_andb.
  rewrite nth_combine_default; auto.
Qed.

(** Length of combine is minimum of input lengths *)
Lemma length_combine : forall {A B : Type} (l1 : list A) (l2 : list B),
  length (combine l1 l2) = min (length l1) (length l2).
Proof.
  intros A B l1 l2.
  generalize dependent l2.
  induction l1 as [|a l1' IH]; intros l2.
  - simpl. reflexivity.
  - destruct l2 as [|b l2'].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.
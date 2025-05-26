Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FSetList.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Import ListNotations.

(** * Basic Types *)

(** Physical address representation *)
Definition PhysAddr := Z.

(** Represents a page size *)
Record PageSize := mkPageSize {
  size : Z;
  size_positive : Z.gt size 0
}.

(** A physical frame with a specific page size *)
Record PhysFrame (S : PageSize) := mkPhysFrame {
  start_address : PhysAddr;
  (* Ensure frame is properly aligned *)
  frame_aligned : (Z.modulo start_address (size S)) = 0%Z
}.

(** A range of physical frames *)
Record PhysFrameRange (S : PageSize) := mkPhysFrameRange {
  start_frame : PhysFrame S;
  end_frame : PhysFrame S;
  (* Ensure start <= end *)
  range_valid : Z.le (start_address S start_frame) (start_address S end_frame)
}.

(** * Bitmap representation *)

Definition BitArray := list bool.

(** * BitmapAllocator *)

Record BitmapAllocator (S : PageSize) := mkBitmapAllocator {
  allocated : BitArray; (* Tracks allocated frames *)
  valid : BitArray;     (* Tracks valid frames *)
  range : PhysFrameRange S;
  
  (* Ensure bitvectors have correct length *)
  bitmap_size_ok : length allocated = length valid;
  
  (* Ensure bitmap is large enough for the range *)
  range_covered : length allocated = 
    Z.to_nat ((start_address S (end_frame S range) - 
               start_address S (start_frame S range)) / size S)
}.

(** * Helper Lemmas *)

(** Length of a list created by repeating an element n times equals n *)
Lemma eq_length_repeat {A : Type} (x : A) (n : nat) : length (repeat x n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma size_nonzero {S : PageSize} : 0%Z <> size S.
Proof.
  intro H.
  pose proof (size_positive S) as G.
  rewrite H in G. 
  lia.
Qed.

(** * Utility Functions *)

(** Calculate index in bitmap for a given frame *)
Definition frame_idx {S : PageSize} (alloc : BitmapAllocator S) (frame : PhysFrame S) : option nat :=
  let start_addr := start_address S (start_frame S (range S alloc)) in
  let frame_addr := start_address S frame in
  let end_addr := start_address S (end_frame S (range S alloc)) in
  if (Z.ltb frame_addr start_addr) || (Z.ltb end_addr frame_addr) then
    None
  else
    Some (Z.to_nat ((frame_addr - start_addr) / size S)).

(** Get frame at a specific index *)
Program Definition frame_at_idx {S : PageSize} (alloc : BitmapAllocator S) (idx : nat) : option (PhysFrame S) :=
  let start_addr := start_address S (start_frame S (range S alloc)) in
  let max_idx := Z.to_nat ((start_address S (end_frame S (range S alloc)) - start_addr) / size S) in
  if idx <? max_idx then
    let addr := Z.add start_addr (Z.mul (Z.of_nat idx) (size S)) in
    Some {| start_address := addr; frame_aligned := _ |} 
  else
    None.
Next Obligation.
  destruct (start_frame S (range S alloc)) as [start_addr aligned_proof].
  simpl in *.
  rewrite Z.add_mod by (apply Z.neq_sym; apply size_nonzero).
  
  (* The start address is already aligned *)
  rewrite aligned_proof.
  simpl.
  rewrite Z.mod_mod by (apply Z.neq_sym; apply size_nonzero).
  apply Z.mod_mul.
  apply Z.neq_sym.
  apply size_nonzero.
Qed.

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

(** * Core Functions *)

(** Create a new bitmap allocator *)
Definition new_allocator {S : PageSize} (r : PhysFrameRange S) : BitmapAllocator S :=
  let num_frames := 
    Z.to_nat ((start_address S (end_frame S r) - start_address S (start_frame S r)) / size S) in
  let alloc_bits := repeat false num_frames in
  let valid_bits := repeat false num_frames in
  {|
    allocated := alloc_bits;
    valid := valid_bits;
    range := r;
    bitmap_size_ok := eq_refl;
    range_covered := eq_length_repeat false num_frames
  |}.

Fixpoint update_range_bits (bits : BitArray) (start : nat) (current : nat) (end_idx : nat) (value : bool) : BitArray :=
  match bits, current with
  | [], _ => []
  | b :: bs, n =>
      if (start <=? n) && (n <=? end_idx) 
      then value :: update_range_bits bs start (S current) end_idx value
      else b :: update_range_bits bs start (S current) end_idx value
  end.

Lemma update_range_bits_preserve_length :
  forall S alloc start_idx end_idx is_valid curr_idx,
    length (update_range_bits (valid S alloc) start_idx curr_idx end_idx is_valid) = 
    length (valid S alloc).
Proof.
  Proof.
  intros S alloc start_idx end_idx is_valid curr_idx.
  generalize dependent curr_idx.
  induction (valid S alloc) as [|h t IH].
  - intros. simpl. reflexivity.
  - intros. simpl.
    destruct ((start_idx <=? curr_idx) && (curr_idx <=? end_idx)) eqn:E.
    + simpl. f_equal. apply IH.
    + simpl. f_equal. apply IH.
Qed.

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

(** Mark a range of frames as valid or invalid *)
Program Definition mark_valid {S : PageSize} (alloc : BitmapAllocator S) 
                      (frame_range : PhysFrameRange S) (is_valid : bool) : option (BitmapAllocator S) :=
  match frame_idx alloc (start_frame S frame_range), 
        frame_idx alloc (end_frame S frame_range) with
  | Some start_idx, Some end_idx =>
    (* Update the valid bitmap from start_idx to end_idx *)
    let new_valid := update_range_bits (valid S alloc) start_idx 0 end_idx is_valid in
    Some {|
      allocated := allocated S alloc;
      valid := new_valid;
      range := range S alloc;
      bitmap_size_ok := _; 
      range_covered := range_covered S alloc
    |}
  | _, _ => None (* Range is outside our allocator's range *)
  end.
Next Obligation.
  rewrite (update_range_bits_preserve_length S alloc start_idx end_idx is_valid 0).
  apply (bitmap_size_ok S alloc).
Qed.

(** Get available bitmap (valid AND NOT allocated) *)
Definition available {S : PageSize} (alloc : BitmapAllocator S) : BitArray :=
  bitand (valid S alloc) (bitnot (allocated S alloc)).

(** Allocate a specific frame *)
Program Definition allocate_frame {S : PageSize} (alloc : BitmapAllocator S) : option (PhysFrame S * BitmapAllocator S) :=
  match first_one_from_zero (available alloc) with
  | Some idx =>
    match frame_at_idx alloc idx with
    | Some frame =>
      let new_allocated := set_bit (allocated S alloc) idx true in
      let new_alloc := {|
        allocated := new_allocated;
        valid := valid S alloc;
        range := range S alloc;
        bitmap_size_ok := _; 
        range_covered := range_covered S alloc
      |} in
      Some (frame, new_alloc)
    | None => None
    end
  | None => None
  end.
  Next Obligation.
    rewrite set_bit_preserves_length.
    apply (bitmap_size_ok S alloc).
  Qed.
  Next Obligation.
    rewrite set_bit_preserves_length.
    reflexivity.
  Qed.


Definition size_4k : PageSize := {|
  size := 4096%Z;
  size_positive := eq_refl
|}.

Definition size_2m : PageSize := {|
  size := 2097152%Z;
  size_positive := eq_refl
|}.

Definition page_size_2m : Z := 2097152%Z.

Definition range_0_32m : PhysFrameRange size_2m.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 33554432%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_0_8k : PhysFrameRange size_4k.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 8192%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_0_128k : PhysFrameRange size_4k.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 131072%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined. 


Definition marked_allocator_0_8k : BitmapAllocator size_4k :=
  match mark_valid (new_allocator range_0_8k) range_0_8k true with
  | Some alloc => alloc
  | None => new_allocator range_0_8k
  end.

Definition marked_allocator_0_128k : BitmapAllocator size_4k :=
  match mark_valid (new_allocator range_0_128k) range_0_128k true with
  | Some alloc => alloc
  | None => new_allocator range_0_128k
  end.

Definition marked_allocator_0_32m : BitmapAllocator size_2m :=
  match mark_valid (new_allocator range_0_32m) range_0_32m true with
  | Some alloc => alloc
  | None => new_allocator range_0_32m
  end.

Compute let alloc := marked_allocator_0_128k in
  match allocate_frame alloc with
  | Some (frame1, alloc1) => 
      (start_address _ frame1,
       match allocate_frame alloc1 with
       | Some (frame2, alloc2) => 
           (start_address _ frame2, 
            allocated _ alloc2)
       | None => ((-1)%Z, [])
       end)
  | None => ((-1)%Z, ((-1)%Z, []))
  end.



(** Deallocate a frame *)
Program Definition deallocate_frame {S : PageSize} (alloc : BitmapAllocator S) 
                           (frame : PhysFrame S) : option (BitmapAllocator S) :=
  match frame_idx alloc frame with
  | Some idx =>
    if negb (get_bit (valid S alloc) idx) then
      None (* Frame is not valid in this allocator *)
    else if negb (get_bit (allocated S alloc) idx) then
      None (* Frame was not allocated in this allocator *)
    else
      let new_allocated := set_bit (allocated S alloc) idx false in
      Some {|
        allocated := new_allocated;
        valid := valid S alloc;
        range := range S alloc;
        bitmap_size_ok := _; 
        range_covered := range_covered S alloc
      |}
  | None => None (* Frame is outside our range *)
  end.
Next Obligation.
  rewrite set_bit_preserves_length.
  apply (bitmap_size_ok S alloc).
Qed.
Next Obligation.
  rewrite set_bit_preserves_length.
  reflexivity.
Qed.

(* Helper Lemmas *)

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

Search (S _ < S _).

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


(** * Theorems and Properties *)

(** A newly created allocator has no allocated frames *)
Theorem new_allocator_no_alloc : forall {S : PageSize} (r : PhysFrameRange S),
  count_ones (allocated S (new_allocator r)) = 0.
Proof.
  intros S r.
  unfold new_allocator.
  simpl.
  induction (Z.to_nat ((start_address S (end_frame S r) - start_address S (start_frame S r)) / size S)); simpl; auto.
Qed.

(** After allocating a frame, the number of allocated frames increases by 1 *)
Theorem allocate_frame_increases_count : forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  allocate_frame alloc = Some (frame, new_alloc) ->
  count_ones (allocated S new_alloc) = count_ones (allocated S alloc) + 1.
Proof.
  intros S alloc frame new_alloc H_alloc.
  unfold allocate_frame in H_alloc.
 
  destruct (first_one_from_zero (available alloc)) eqn:H_first; [|discriminate].
  destruct (frame_at_idx alloc n) eqn:H_frame; [|discriminate].
  injection H_alloc as H_eq1 H_eq2.

  assert (H_avail_true: get_bit (available alloc) n = true).
  {
    unfold first_one_from_zero in H_first.
    apply first_one_returns_true in H_first.
    assumption.
  }
  
  assert (H_not_allocated: get_bit (allocated S alloc) n = false).
  {
    rewrite available_correct in H_avail_true.
    apply Bool.andb_true_iff in H_avail_true.
    destruct H_avail_true as [_ H_neg].
    apply Bool.negb_true_iff in H_neg. assumption.
  }

  assert (H_idx_bound: n < length (allocated S alloc)).
  {
    apply first_one_in_bounds in H_first.
    rewrite <- available_length_eq.
    assumption.
  }
  rewrite <- H_eq2. 
  apply set_bit_false_to_true_increases_count; assumption.
Qed.

(** After deallocating a frame, the number of allocated frames decreases by 1 *)
Theorem deallocate_frame_decreases_count : forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  deallocate_frame alloc frame = Some new_alloc ->
  count_ones (allocated S new_alloc) = count_ones (allocated S alloc) - 1.
Proof.
  intros S alloc frame new_alloc H_dealloc.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) eqn:H_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_eq.
  
  assert (H_frame_valid: get_bit (valid S alloc) n = true).
  {
    apply Bool.negb_false_iff in H_valid. assumption.
  }
  
  assert (H_frame_allocated: get_bit (allocated S alloc) n = true).
  {
    apply Bool.negb_false_iff in H_allocated. assumption.
  }
  
  assert (H_idx_bound: n < length (allocated S alloc)).
  { unfold get_bit in H_frame_valid.
    destruct (n <? length (valid S alloc)) eqn:H_n_bound.
    - apply Nat.ltb_lt in H_n_bound.
      rewrite (bitmap_size_ok S alloc).
      exact H_n_bound.
    - apply Nat.ltb_ge in H_n_bound.
      rewrite nth_overflow in H_frame_valid.
      + discriminate H_frame_valid.
      + exact H_n_bound.
  }
  
  rewrite <- H_eq.
  apply set_bit_true_to_false_decreases_count; assumption.
Qed.

(** A frame cannot be allocated twice without being deallocated *)
Theorem no_double_allocation : forall {S : PageSize} (alloc : BitmapAllocator S) frame1 new_alloc1 frame2 new_alloc2,
  allocate_frame alloc = Some (frame1, new_alloc1) ->
  allocate_frame new_alloc1 = Some (frame2, new_alloc2) ->
  frame1 <> frame2.
Proof.
  
Admitted.

(** * Process and System Types *)

(** Process identifier *)
Definition ProcessId := nat.

(** Virtual address representation *)
Definition VirtAddr := Z.

(** * mmap Protection and Flags *)

(** mmap Protection flags *)
Inductive MmapProtection : Type :=
  | PROT_READ
  | PROT_WRITE
  | PROT_EXEC.

Definition MmapProtectionSet := list MmapProtection.

Definition mmap_prot_eq (f1 f2 : MmapProtection) : bool :=
  match f1, f2 with
  | PROT_READ, PROT_READ => true
  | PROT_WRITE, PROT_WRITE => true
  | PROT_EXEC, PROT_EXEC => true
  | _, _ => false
  end.

(** Check if a protection set contains a specific protection *)
Definition prot_contains (prots: MmapProtectionSet) (p: MmapProtection) : bool :=
  existsb (fun x => mmap_prot_eq x p ) prots.

(** Check if a protection set contains a specific protection *)

(** mmap Flags *)
Inductive MmapFlag : Type :=
  | MAP_PRIVATE
  | MAP_FIXED
  | MAP_ANONYMOUS.

Definition MmapFlagSet := list MmapFlag.

Definition mmap_flag_eq (f1 f2 : MmapFlag) : bool :=
  match f1, f2 with
  | MAP_PRIVATE, MAP_PRIVATE => true
  | MAP_FIXED, MAP_FIXED => true
  | MAP_ANONYMOUS, MAP_ANONYMOUS => true
  | _, _ => false
  end.

(** Check if a flag set contains a specific flag *)
Definition flag_contains (flags: MmapFlagSet) (f: MmapFlag) : bool :=
  existsb (fun x => mmap_flag_eq x f) flags.

(** * Error Representation *)

(** Error types for mmap operations *)
Inductive Errno : Type :=
  | ENOERR    (* No error *)
  | EINVAL    (* Invalid argument *)
  | ENOMEM    (* Not enough memory *)
  | EACCES    (* Permission denied *).

(** * Page Tables and Memory Representation *)

(** Page table flags *)
Inductive PageTableFlag : Type :=
  | PF_PRESENT
  | PF_WRITABLE
  | PF_USER_ACCESSIBLE
  | PF_NO_EXECUTE
  | PF_ENCRYPTED.

Definition PageTableFlagSet := list PageTableFlag.

Definition ptflag_eq (f1 f2 : PageTableFlag) : bool :=
  match f1, f2 with
  | PF_PRESENT, PF_PRESENT => true
  | PF_WRITABLE, PF_WRITABLE => true
  | PF_USER_ACCESSIBLE, PF_USER_ACCESSIBLE => true
  | PF_NO_EXECUTE, PF_NO_EXECUTE => true
  | PF_ENCRYPTED, PF_ENCRYPTED => true
  | _, _ => false
  end.

(** Check if a flag set contains a specific flag *)
Definition ptflag_contains (flags: PageTableFlagSet) (f: PageTableFlag) : bool :=
  existsb (fun x => ptflag_eq x f) flags.

(** A mapping entry in a page table *)
Record PageTableEntry := mkPageTableEntry {
  pte_virt_addr : VirtAddr;
  pte_phys_addr : PhysAddr;
  pte_page_size : PageSize;
  pte_flags : PageTableFlagSet
}.

(** The page table for a process *)
Definition PageTable := list PageTableEntry.

Module VirtAddrMap := FMapAVL.Make(Z_as_OT).

(** A memory mapping in a process's address space *)
Record MemoryMapping := mkMemoryMapping {
  mm_start_addr : VirtAddr;
  mm_size : Z;
}.

(** A process with its page table and memory mappings *)
Record Process := mkProcess {
  proc_id : ProcessId;
  proc_page_table : PageTable;
  proc_memory_mappings : VirtAddrMap.t MemoryMapping;
}.

Axiom proc_id_injective : forall p1 p2,
  proc_id p1 = proc_id p2 -> p1 = p2.

(** The system state with all processes and the frame allocator *)
Record SystemState (S : PageSize) := mkSystemState {
  processes : list Process;
  frame_allocator : BitmapAllocator S;
  
  (* System invariant: process IDs must be unique *)
  sys_unique_pids : forall p1 p2,
    In p1 processes -> In p2 processes -> 
    proc_id p1 = proc_id p2 -> p1 = p2;
  
}.

(** Convert MmapProtection to PageTableFlags *)
Definition prot_to_ptflags (prots: MmapProtectionSet) : PageTableFlagSet :=
  PF_PRESENT :: PF_USER_ACCESSIBLE :: PF_ENCRYPTED ::
  (if prot_contains prots PROT_EXEC then [] else [PF_NO_EXECUTE]) ++
  (if prot_contains prots PROT_WRITE then [PF_WRITABLE] else []).

(** Check if a virtual address range is unallocated in a page table *)
Definition is_range_unallocated (pt: PageTable) (start: VirtAddr) (mapping_size: Z) : bool :=
  forallb (fun pte => 
    let pte_end := (pte_virt_addr pte + size (pte_page_size pte))%Z in
    let request_end := (start + mapping_size)%Z in
    (pte_end <=? start)%Z || (request_end <=? pte_virt_addr pte)%Z
  ) pt.

(** Find a process by ID *)
Definition find_process {S : PageSize} (sys: SystemState S) (pid: ProcessId) : option Process :=
  find (fun p => if proc_id p =? pid then true else false) (processes S sys).

(** Check if a page size is supported *)
Definition is_supported_page_size (ps: PageSize) : bool :=
  let sz := size ps in
  ((Z.eqb sz 4096) || (Z.eqb sz 2097152) || (Z.eqb sz 1073741824)).

(* Create a 2MiB page size constant *)
Program Definition PAGE_SIZE_2MB : PageSize := 
  {| size := 2097152; size_positive := _ |}.
Next Obligation.
simpl. lia.
Qed.

(** Align an address to a page size boundary *)
Definition align_up (addr: Z) (ps: PageSize) : Z :=
  let mask := Z.sub (size ps) 1 in
  Z.mul (Z.div (Z.add addr mask) (size ps)) (size ps).

Compute align_up 2097152%Z PAGE_SIZE_2MB.

(** Create a range of page table entries *)
Fixpoint create_pte_range_nat
  (vaddr: VirtAddr) (paddr: PhysAddr) (count: nat) (ps: PageSize) (flags: PageTableFlagSet)
  : list PageTableEntry :=
  match count with
  | O => []
  | S n => 
    let pte := {|
      pte_virt_addr := vaddr;
      pte_phys_addr := paddr;
      pte_page_size := ps;
      pte_flags := flags
    |} in
    let sz := size ps in
    pte :: create_pte_range_nat (vaddr + sz)%Z (paddr + sz)%Z n ps flags
  end.

Definition create_pte_range
  (vaddr: VirtAddr) (paddr: PhysAddr) (remaining: Z) (ps: PageSize) (flags: PageTableFlagSet)
  : list PageTableEntry :=
  if Z.leb remaining 0 then []
  else
    let sz := size ps in
    let count := Z.to_nat (Z.div (remaining + sz - 1) sz) in (* Ceiling division *)
    create_pte_range_nat vaddr paddr count ps flags.


Fixpoint alloc_frames_nat {S: PageSize}(alloc: BitmapAllocator S) (n: nat) (acc: list (PhysFrame S)) : 
          list (PhysFrame S) * BitmapAllocator S + Errno :=
        match n with
        | O => inl (acc, alloc)
        | S n' =>
          match allocate_frame alloc with
          | Some (frame, new_alloc) => alloc_frames_nat new_alloc n' (frame :: acc)
          | None => inr ENOMEM
          end
        end.

(* Definition allocate_frames (alloc: BitmapAllocator size_4k) (n: nat) : 
          list (PhysFrame size_4k) * BitmapAllocator size_4k + Errno :=
  alloc_frames_nat alloc n [].


Compute 
  let alloc := marked_allocator_0_128k in
  match allocate_frames alloc 2 with
  | inl (frames, new_alloc) => 
      (map (fun f => start_address _ f) frames,
       valid _ new_alloc, 
       allocated _ new_alloc)
  | inr _ => ([], [], [])
  end. *)

(* Function to check if an address is aligned to page size *)
Definition is_aligned (addr : VirtAddr) (ps : PageSize) : bool :=
  Z.eqb (Z.modulo addr (size ps)) 0.

(* Representation of a slice of bytes (return type of mmap) *)
Record ByteSlice := mkByteSlice {
  slice_addr : VirtAddr;
  slice_size : Z;
}.

(* Result type for mmap operation *)
Inductive MmapResult :=
  | MmapSuccess (slice : ByteSlice)
  | MmapError (error : Errno).

(* Helper to allocate frames from the BitmapAllocator *)
Fixpoint allocate_frames {S : PageSize} (count : nat) (alloc : BitmapAllocator S) 
                        : option (list (PhysFrame S) * BitmapAllocator S) :=
  match count with
  | O => Some ([], alloc)
  | S n =>
    match allocate_frame alloc with
    | Some (frame, new_alloc) =>
      match allocate_frames n new_alloc with
      | Some (frames, final_alloc) => Some (frame :: frames, final_alloc)
      | None => None
      end
    | None => None
    end
  end.

(* Function to replace a process in a list of processes *)
Fixpoint replace_process (old_proc : Process) (new_proc : Process) (procs : list Process) : list Process :=
  match procs with
  | [] => []
  | p :: ps =>
    if proc_id p =? proc_id old_proc
    then new_proc :: ps
    else p :: replace_process old_proc new_proc ps
  end.

(* Function to add a memory mapping to a process *)
Definition add_mapping (proc : Process) (addr : VirtAddr) (mapping : MemoryMapping) : Process :=
  {|
    proc_id := proc_id proc;
    proc_page_table := proc_page_table proc;
    proc_memory_mappings := VirtAddrMap.add addr mapping (proc_memory_mappings proc);
  |}.

(* Function to add page table entries to a process *)
Definition add_ptes (proc : Process) (ptes : list PageTableEntry) : Process :=
  {|
    proc_id := proc_id proc;
    proc_page_table := proc_page_table proc ++ ptes;
    proc_memory_mappings := proc_memory_mappings proc;
  |}.

(* The mmap syscall implementation *)
Program Definition mmap (sys : SystemState PAGE_SIZE_2MB) (pid : ProcessId) 
                (addr_opt : option VirtAddr) (sz : Z) 
                (prot : MmapProtectionSet) (flags : MmapFlagSet) 
                : (MmapResult * SystemState PAGE_SIZE_2MB ) :=
  
  (* Check if size is valid *)
  if Z.leb sz 0 then
    (MmapError EINVAL, sys)
  
  (* Check if required flags are present *)
  else if negb (flag_contains flags MAP_ANONYMOUS) || negb (flag_contains flags MAP_PRIVATE) then
    (MmapError EINVAL, sys)
    
  (* Find the process *)
  else
    match find_process sys pid with
    | None => (MmapError EINVAL, sys)
    | Some proc =>
      
      (* Determine starting address based on flags *)
      let addr_result :=
        if flag_contains flags MAP_FIXED then
          (* For MAP_FIXED, use the exact address *)
          match addr_opt with
          | None => inr EINVAL
          | Some a =>
            if is_aligned a PAGE_SIZE_2MB && (Z.geb a (size PAGE_SIZE_2MB)) then
              inl a
            else
              inr EINVAL
          end
        else
          (* For non-MAP_FIXED, we can adjust the address *)
          let base_addr :=
            match addr_opt with
            | None => size PAGE_SIZE_2MB
            | Some a => Z.max a (size PAGE_SIZE_2MB)
            end in
          inl (align_up base_addr PAGE_SIZE_2MB)
      in
      
      match addr_result with
      | inr err => (MmapError err, sys)
      | inl start_addr =>
        
        (* Round up size to page boundary *)
        let aligned_size := align_up sz PAGE_SIZE_2MB in
        
        (* Check if address range is free *)
        if negb (is_range_unallocated (proc_page_table proc) start_addr aligned_size) then
          (MmapError ENOMEM, sys)
        else
          
          (* Calculate number of pages needed *)
          let frame_count := Z.to_nat (Z.div aligned_size (size PAGE_SIZE_2MB)) in
          
          (* Allocate physical frames *)
          match allocate_frames frame_count (frame_allocator PAGE_SIZE_2MB sys) with
          | None => (MmapError ENOMEM, sys)
          | Some (frames, new_allocator) =>
            
            (* Convert protection flags to page table flags *)
            let pt_flags := prot_to_ptflags prot in
            
            (* Create page table entries *)
            let ptes := 
              match frames with
              | [] => [] (* Should never happen if frame_count > 0 *)
              | first_frame :: _ =>
                create_pte_range 
                  start_addr 
                  (start_address PAGE_SIZE_2MB first_frame) 
                  aligned_size 
                  PAGE_SIZE_2MB 
                  pt_flags
              end in
            
            (* Create memory mapping record *)
            let mapping := {|
              mm_start_addr := start_addr;
              mm_size := aligned_size;
            |} in
            
            (* Update process with new page table entries and mapping *)
            let new_proc := add_ptes (add_mapping proc start_addr mapping) ptes in
            
            (* Update system state *)
            let new_processes := replace_process proc new_proc (processes PAGE_SIZE_2MB sys) in
            
            (* Create new system state *)
            let new_sys := {|
              processes := new_processes;
              frame_allocator := new_allocator;
              sys_unique_pids := _;
            |} in
            
            (* Return success with the mapped memory slice *)
            let result := MmapSuccess (mkByteSlice start_addr aligned_size) in
            (result, new_sys)
          end
      end
    end.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Definition frame_0 : PhysFrame size_4k. 
Proof. refine {|
  start_address := 0%Z;
  frame_aligned := _ 
|}.
  simpl. reflexivity.
Defined.

Definition frame_8k : PhysFrame size_4k. 
Proof. refine {|
  start_address := 8192%Z;
  frame_aligned := _
|}.
  simpl. reflexivity.
Defined.


(* Create an empty system state *)
Program Definition empty_system_state (S : PageSize) (r : PhysFrameRange S) : SystemState S := 
  {|
    processes := [];
    frame_allocator := new_allocator r;
    sys_unique_pids := _;
  |}.
Next Obligation.
  contradiction.
Qed.

Program Definition one_process_system_state (S : PageSize) (r : PhysFrameRange S) (pid : ProcessId) : SystemState S := 
  {|
    processes := [{| proc_id := pid; proc_page_table := []; proc_memory_mappings := VirtAddrMap.empty MemoryMapping |}];
    frame_allocator := new_allocator r;
    sys_unique_pids := _;
  |}.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Program Definition marked_process_system_state (S : PageSize) (r : PhysFrameRange S) (pid : ProcessId) : SystemState S :=
  match mark_valid (new_allocator r) r true with
  | Some marked_alloc =>
    {|
      processes := [{| proc_id := pid; proc_page_table := []; 
                       proc_memory_mappings := VirtAddrMap.empty MemoryMapping |}];
      frame_allocator := marked_alloc;
      sys_unique_pids := _;
    |}
  | None => one_process_system_state S r pid
  end.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Definition range_0_64m : PhysFrameRange PAGE_SIZE_2MB.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 67108864%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_128mb_512mb : PhysFrameRange PAGE_SIZE_2MB.
Proof.
  refine {|
    start_frame := {| start_address := 134217728%Z; frame_aligned := _ |};
    end_frame := {| start_address := 536870912%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.


(* Test cases for mmap function *)

(* Not allowed to map since no process with pid 1 *)
Compute (mmap (empty_system_state PAGE_SIZE_2MB range_0_64m) 1 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Not enough memory since bitmapallocator not initialized *)
Compute (mmap (one_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Mapping a single page *)
Compute (mmap (marked_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 
         (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Page table after mapping a single page *)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 
         (Some 4096666%Z) 819254%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | (MmapSuccess _, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | _ => []
         end.

(* Mapping a range of pages *)
Compute (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Page table after mapping a range of pages *)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | ( MmapSuccess _, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | _ => []
         end.

(* Returned starting virtual address*)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | ( MmapSuccess bs, new_sys) => 
             bs 
         | _ => mkByteSlice 0%Z 0%Z
         end.

Compute align_up 8192000%Z PAGE_SIZE_2MB.

(* Not allowed to map since no process with pid 1 *)
(*
(* Not allowed to map *)
Compute (mmap (empty_system_state size_4k range_0_8k) 1 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS; MAP_FIXED]).

(* Not enough memory since bitmapallocator not initialized *)
Compute (mmap (one_process_system_state size_4k range_0_8k 0) 0 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

Compute (mmap (marked_process_system_state size_4k range_0_8k 0) 0 
         (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

Compute match (mmap (marked_process_system_state size_4k range_0_128k 0) 0 
         (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | inl (_, new_sys) => allocated _ (frame_allocator _ new_sys)
         | inr err => []
         end.

Compute match (mmap (marked_process_system_state size_4k range_0_128k 0) 0 
         (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | inl (_, new_sys) => valid _ (frame_allocator _ new_sys)
         | inr err => []
         end.

Compute match (mmap (marked_process_system_state size_4k range_0_128k 0) 0 
         (Some 4096%Z) 816%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | inl (_, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | inr err => []
         end.

Compute match (mmap (marked_process_system_state size_2m range_0_32m 0) 0 
         (Some 4096000%Z) 819280%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | inl (_, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | inr err => []
         end. *)
(** Safety properties - These would need to be proven *)

(** After mmap, the allocated memory is accessible to the process *)
Theorem mmap_memory_accessible : forall (sys: SystemState PAGE_SIZE_2MB) pid addr size prot flags vaddr new_sys,
  mmap sys pid addr size prot flags = (MmapSuccess (mkByteSlice vaddr size), new_sys) ->
  exists proc,
    In proc (processes PAGE_SIZE_2MB new_sys) /\
    proc_id proc = pid /\
    exists mapping,
      VirtAddrMap.find vaddr (proc_memory_mappings proc) = Some mapping /\
      mm_start_addr mapping = vaddr /\
      mm_size mapping = align_up size PAGE_SIZE_2MB.

(** No overlapping allocations *)
Theorem mmap_no_overlap : forall (sys: SystemState PAGE_SIZE_2MB) pid1 pid2 addr1 addr2 size1 size2 prot1 prot2 flags1 flags2 vaddr1 vaddr2 new_sys1 new_sys2,
  mmap sys pid1 addr1 size1 prot1 flags1 = (MmapSuccess (mkByteSlice vaddr1 size1), new_sys1)  ->
  mmap new_sys1 pid2 addr2 size2 prot2 flags2 = (MmapSuccess (mkByteSlice vaddr2 size2), new_sys2) ->
  (pid1 <> pid2 \/ 
   Z.le (Z.add vaddr1 (align_up size1 S)) vaddr2 \/ 
   Z.le (Z.add vaddr2 (align_up size2 S)) vaddr1).

(** Physical frames are properly accounted for in the allocator *)
Theorem mmap_frames_allocated : forall {S: PageSize} (sys: SystemState S) pid addr sz prot flags vaddr new_sys,
  mmap sys pid addr sz prot flags = inl (vaddr, new_sys) ->
  count_ones (allocated S (frame_allocator S new_sys)) = 
  count_ones (allocated S (frame_allocator S sys)) + 
  Z.to_nat ((align_up sz S) / (size S)).

(** MAP_FIXED respects the provided address *)
Theorem mmap_fixed_respects_addr : forall {S: PageSize} (sys: SystemState S) pid addr size prot flags vaddr new_sys,
  flag_contains flags MAP_FIXED = true ->
  mmap sys pid (Some addr) size prot flags = inl (vaddr, new_sys) ->
  vaddr = addr.

(** Protection flags are properly set in the page table entries *)
Theorem mmap_protection_set : forall {S: PageSize} (sys: SystemState S) pid addr size prot flags vaddr new_sys proc pte,
  mmap sys pid addr size prot flags = inl (vaddr, new_sys) ->
  In proc (processes S new_sys) ->
  proc_id proc = pid ->
  In pte (proc_page_table proc) ->
  Z.ge (pte_virt_addr pte) vaddr ->
  Z.lt (pte_virt_addr pte) (Z.add vaddr (align_up size S)) ->
  pte_flags pte = prot_to_ptflags prot.

(** * Usage *)

(** Common page sizes *)
(* 

Definition size_2m : PageSize := {|
  size := 2097152%Z; (* 2MB = 2 * 1024 * 1024 *)
  size_positive := eq_refl
|}. *)

(** Create a 4K page size *)
(* Definition size_4k : PageSize := {|
  size := 4096;
  size_positive := eq_refl
|}.

(** Create a physical frame at address 0 *)
Definition frame_0 : PhysFrame size_4k := {|
  start_address := 0%Z;
  frame_aligned := eq_refl
|}.

(** Create a physical frame at address 4K *)
Definition frame_4k : PhysFrame size_4k.
Proof.
  refine {|
    start_address := 4096%Z;
    frame_aligned := _
  |}.
  simpl. (* Simplify the goal *)
  unfold size_4k. simpl.
  apply Z.mod_same.
  discriminate.
Defined.

(** Create a frame range from 0 to 8K *)
Definition range_0_8k : PhysFrameRange size_4k. 
Proof.
  refine {|
  start_frame := frame_0;
  end_frame := {| start_address := 8192%Z; 
  frame_aligned := _ |};
  range_valid := _
|}.
  simpl. unfold Z.le. simpl. discriminate.
  Unshelve. simpl. reflexivity.
  Defined.

(** Create an allocator for the range *)
Definition example_allocator := new_allocator range_0_8k.

(** Mark the entire range as valid *)
Definition marked_allocator := 
  match mark_valid example_allocator range_0_8k true with
  | Some alloc => alloc
  | None => example_allocator
  end.

Compute frame_idx (new_allocator range_0_8k) frame_0.

Definition frame_2000th : PhysFrame size_4k.
Proof.
  refine {|
    start_address := (2000 * 4096)%Z;
    frame_aligned := _
  |}.
  simpl. unfold size_4k. simpl. reflexivity.
  Defined.

Definition frame_5gb : PhysFrame size_4k.
Proof.
  refine {|
    start_address := (1310720 * 4096)%Z;
    frame_aligned := _
  |}.
  simpl. unfold size_4k. simpl. reflexivity.
  Defined.

Definition range_0_5gb : PhysFrameRange size_4k.
Proof.
  refine {|
  start_frame := frame_0;
  end_frame := frame_5gb;
  range_valid := _
|}.
  simpl. lia. Defined.

(** Try to allocate a frame *)
Definition allocation_result := allocate_frame marked_allocator.

(* What index is the allocated frame in? *)
Compute match allocation_result with
| Some (frame, _) => frame_idx marked_allocator frame
| None => None
end.

(** Test allocation **)

Require Import Coq.Strings.String.
Open Scope string_scope.

(* Check if allocation succeeds *)
Compute match allocation_result with
  | Some _ => "Allocation succeeded"%string
  | None => "Allocation failed"%string
  end.

(* Extract the allocated frame and new allocator state *)
Definition allocated_frame := 
  match allocation_result with
  | Some (frame, _) => Some frame
  | None => None
  end.

Compute allocated_frame.

Definition post_alloc_state := 
  match allocation_result with
  | Some (_, alloc) => Some alloc
  | None => None
  end.

(* Check if the frame is marked as allocated *)
Compute 
  match allocated_frame, post_alloc_state with
  | Some frame, Some alloc => 
      match frame_idx alloc frame with
      | Some idx => get_bit (allocated _ alloc) idx
      | None => false
      end
  | _, _ => false
  end.

(* Check if the frame is marked as valid *)
Compute 
  match allocated_frame, post_alloc_state with
  | Some frame, Some alloc => 
      match frame_idx alloc frame with
      | Some idx => get_bit (valid _ alloc) idx
      | None => false
      end
  | _, _ => false
  end.

(** Test deallocation **)

(* Try to deallocate the frame *)
Definition deallocation_result :=
  match allocated_frame, post_alloc_state with
  | Some frame, Some alloc => deallocate_frame alloc frame
  | _, _ => None
  end.

(* Check if deallocation succeeds *)
Compute
  match deallocation_result with
  | Some _ => "Deallocation succeeded"%string
  | None => "Deallocation failed"%string
  end.
  

(* Check if frame is no longer allocated after deallocation *)
Compute
  match allocated_frame, deallocation_result with
  | Some frame, Some alloc =>
      match frame_idx alloc frame with
      | Some idx => get_bit (allocated _ alloc) idx
      | None => true (* Should be false if deallocation worked *)
      end
  | _, _ => true
  end.

(* Verify frame is still valid after deallocation *)
Compute
  match allocated_frame, deallocation_result with
  | Some frame, Some alloc =>
      match frame_idx alloc frame with
      | Some idx => get_bit (valid _ alloc) idx
      | None => false
      end
  | _, _ => false
  end.

(* Try allocating again - should reuse the same frame *)
Definition reallocation_result :=
  match deallocation_result with
  | Some alloc => allocate_frame alloc
  | None => None
  end.

(* Check if we get the same frame back *)
Compute
  match allocated_frame, reallocation_result with
  | Some orig_frame, Some (new_frame, _) => 
      Z.eqb (start_address _ orig_frame) (start_address _ new_frame)
  | _, _ => false
  end. *)


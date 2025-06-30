Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
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

Lemma frame_at_idx_injective : forall {S : PageSize} (alloc : BitmapAllocator S) i j frame,
  frame_at_idx alloc i = Some frame ->
  frame_at_idx alloc j = Some frame ->
  i = j.
Proof.
  intros S alloc i j frame H_i H_j.
  unfold frame_at_idx in H_i, H_j.
  
  set (start_addr := start_address S (start_frame S (range S alloc))).
  set (end_addr := start_address S (end_frame S (range S alloc))).
  set (max_idx := Z.to_nat ((end_addr - start_addr) / size S)).
  
  destruct (i <? max_idx) eqn:H_i_bound.
  - destruct (j <? max_idx) eqn:H_j_bound.
    + set (addr_i := Z.add start_addr (Z.mul (Z.of_nat i) (size S))) in H_i.
      set (addr_j := Z.add start_addr (Z.mul (Z.of_nat j) (size S))) in H_j.
      unfold max_idx in H_i_bound.
      unfold max_idx in H_j_bound.
      
      unfold end_addr, start_addr in *.

      rewrite H_i_bound in H_i.
      rewrite H_j_bound in H_j.
    
      injection H_i as H_frame_i.
      injection H_j as H_frame_j.
      
      simpl in *.
      assert (H_addr_eq: addr_i = addr_j).
      {
        rewrite <- H_frame_i in H_frame_j.
        injection H_frame_j as H_addr_eq_direct.
        symmetry.
        exact H_addr_eq_direct.
      }
      unfold addr_i, addr_j in H_addr_eq.
      
      assert (H_mul_eq: ((Z.of_nat i) * size S)%Z = ((Z.of_nat j) * size S)%Z).
      {
        apply Z.add_cancel_l with start_addr.
        exact H_addr_eq.
      }
      
      assert (H_of_nat_eq: Z.of_nat i = Z.of_nat j).
      {
        apply Z.mul_cancel_r with (size S).
        - apply Z.neq_sym. apply size_nonzero.
        - exact H_mul_eq.
      }
      apply Nat2Z.inj in H_of_nat_eq.
      exact H_of_nat_eq.
      
    + unfold max_idx in H_i_bound.
      unfold max_idx in H_j_bound.
      unfold end_addr, start_addr in *.

      rewrite H_i_bound in H_i.
      rewrite H_j_bound in H_j.
      discriminate H_j.
      
  - unfold max_idx in H_i_bound.
    unfold end_addr, start_addr in *.
    rewrite H_i_bound in H_i.
    discriminate H_i.
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

Lemma set_bit_makes_unavailable : forall {S : PageSize} (alloc : BitmapAllocator S) idx,
  idx < length (allocated S alloc) ->
  get_bit (valid S alloc) idx = true ->
  get_bit (allocated S alloc) idx = false ->
  get_bit (bitand (valid S alloc) (bitnot (set_bit (allocated S alloc) idx true))) idx = false.
Proof.
  intros S alloc idx H_bound H_valid H_not_alloc.
  rewrite bitand_get_bit.
  - rewrite H_valid.
    rewrite bitnot_get_bit.
    + rewrite get_bit_set_bit_same; [|assumption].
      simpl.
      reflexivity.
    + rewrite set_bit_preserves_length.
      assumption.
  - rewrite length_bitnot.
    rewrite set_bit_preserves_length.
    symmetry.
    apply (bitmap_size_ok S alloc).
Qed.

Lemma frame_at_idx_frame_idx_inverse : forall {S : PageSize} (alloc : BitmapAllocator S) (idx : nat) (frame : PhysFrame S),
  frame_at_idx alloc idx = Some frame ->
  frame_idx alloc frame = Some idx.
Proof.
  intros S alloc idx frame H_at_idx.
  unfold frame_at_idx in H_at_idx.
  unfold frame_idx.
  
  set (start_addr := start_address S (start_frame S (range S alloc))).
  set (end_addr := start_address S (end_frame S (range S alloc))).
  set (max_idx := Z.to_nat ((end_addr - start_addr) / size S)).

  destruct (idx <? Z.to_nat
  ((start_address S (end_frame S (range S alloc)) - start_address S
  (start_frame S (range S alloc))) / size S)) eqn:H_bound in H_at_idx; [|discriminate].
  
  set (computed_addr := Z.add start_addr (Z.mul (Z.of_nat idx) (size S))).
  injection H_at_idx as H_frame_eq.
  
  assert (H_frame_addr: start_address S frame = computed_addr).
  { simpl in H_frame_eq. rewrite <- H_frame_eq. reflexivity. }
  
  rewrite H_frame_addr.
  
  assert (H_not_lt_start: (Z.ltb computed_addr start_addr) = false).
  {
    apply Z.ltb_ge.
    unfold computed_addr.
    assert (H_pos: (0 <= Z.of_nat idx * size S)%Z).
    {
      apply Z.mul_nonneg_nonneg.
      - apply Nat2Z.is_nonneg.
      - destruct S as [sz pos]. simpl. lia.
    }
    lia.
  }
  
  assert (H_not_gt_end: (Z.ltb end_addr computed_addr) = false).
  {
    apply Z.ltb_ge.
    unfold computed_addr, end_addr, start_addr.
    
    apply Nat.ltb_lt in H_bound.
    unfold max_idx in H_bound.
    
    assert (H_idx_bound: (Z.of_nat idx < (end_addr - start_addr) / size S)%Z).
    {
      rewrite <- Z2Nat.id.
      - apply Nat2Z.inj_lt. exact H_bound.
      - apply Z.div_pos.
        + unfold end_addr, start_addr.
          assert (H_range: (start_address S (start_frame S (range S alloc)) <= 
                           start_address S (end_frame S (range S alloc)))%Z).
          { exact (range_valid S (range S alloc)). }
          lia.
        + destruct S as [sz pos]. simpl. lia.
    }
    
    assert (H_mul_bound: (Z.of_nat idx * size S < end_addr - start_addr)%Z).
    {
      assert (H_pos: (0 < size S)%Z).
      { destruct S as [sz pos]. simpl. apply Z.gt_lt_iff. exact pos. }
      
      assert (H_mul: (Z.of_nat idx * size S < (end_addr - start_addr) / size S * size S)%Z).
      {
        apply Z.mul_lt_mono_pos_r.
        - exact H_pos.
        - exact H_idx_bound.
      }
      
      assert (H_div_mul: ((end_addr - start_addr) / size S * size S <= end_addr - start_addr)%Z).
      {
        pose proof (Z.div_mod (end_addr - start_addr) (size S)) as H_div_mod.
        assert (H_nz: size S <> 0%Z) by (apply Z.neq_sym; apply size_nonzero).
        specialize (H_div_mod H_nz).
        
        assert (H_mod_nonneg: (0 <= (end_addr - start_addr) mod size S)%Z).
        { apply Z.mod_pos_bound. exact H_pos. }
        
        lia.
      }
      
      eapply Z.lt_le_trans.
      - exact H_mul.
      - exact H_div_mul.
    }
    
    lia.
  }
  
  rewrite H_not_lt_start, H_not_gt_end.
  simpl.
  unfold computed_addr.
  assert (H_sub_cancel: (start_addr + Z.of_nat idx * size S - start_addr)%Z = (Z.of_nat idx * size S)%Z).
  { lia. }
  rewrite H_sub_cancel.
  rewrite Z.div_mul.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.neq_sym. apply size_nonzero.
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


(* A frame can only be allocated if it is valid and not already allocated *)
Theorem frame_allocation_valid_unallocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  allocate_frame alloc = Some (frame, new_alloc) ->
  exists idx, 
  frame_idx alloc frame = Some idx /\
  get_bit (valid S alloc) idx = true /\
  get_bit (allocated S alloc) idx = false.
Proof.
  intros S alloc frame new_alloc H_alloc.
  unfold allocate_frame in H_alloc.
  
  destruct (first_one_from_zero (available alloc)) as [n|] eqn:H_first; [|discriminate].
  
  destruct (frame_at_idx alloc n) as [f|] eqn:H_frame; [|discriminate].
  
  injection H_alloc as H_frame_eq H_alloc_eq.
  subst frame.

  exists n.
  
  split.
  - apply frame_at_idx_frame_idx_inverse.
    exact H_frame.
    
  - split. 
    assert (H_avail: get_bit (available alloc) n = true).
    { apply first_one_returns_true. exact H_first. }
    
    unfold available in H_avail.
    rewrite bitand_get_bit in H_avail.
    + destruct (get_bit (valid S alloc) n) eqn:H_valid.
      * reflexivity.
      * simpl in H_avail. discriminate H_avail.
    + apply eq_sym.
      rewrite length_bitnot.
      apply bitmap_size_ok.
    + assert (H_avail: get_bit (available alloc) n = true).
      { apply first_one_returns_true. exact H_first. }
      rewrite available_correct in H_avail.
      apply Bool.andb_true_iff in H_avail.
      destruct H_avail as [_ H_neg].
      apply Bool.negb_true_iff in H_neg.
      exact H_neg.
Qed.
    
(* A frame can only be deallocated if its valid and allocated *)
Theorem frame_deallocation_valid_allocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  deallocate_frame alloc frame = Some new_alloc ->
  exists idx, 
  frame_idx alloc frame = Some idx /\
  get_bit (valid S alloc) idx = true /\
  get_bit (allocated S alloc) idx = true.
Proof.
  intros S alloc frame new_alloc H_dealloc.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) as [n|] eqn:H_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_new_alloc_eq.
  
  exists n.
  
  split.
  - reflexivity.
  
  - split.
    + apply Bool.negb_false_iff in H_valid. exact H_valid.
    + apply Bool.negb_false_iff in H_allocated. exact H_allocated.
Qed.

(* A deallocated frame changes the new bitmaps allocated index to false *)
Theorem deallocate_frame_changes_allocated: forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc idx,
  deallocate_frame alloc frame = Some new_alloc ->
  frame_idx alloc frame = Some idx ->
  get_bit (allocated S new_alloc) idx = false.
Proof.
  intros S alloc frame new_alloc idx H_dealloc H_idx.
  unfold deallocate_frame in H_dealloc.
  
  destruct (frame_idx alloc frame) as [n|] eqn:H_frame_idx; [|discriminate].
  
  destruct (negb (get_bit (valid S alloc) n)) eqn:H_valid; [discriminate|].
  destruct (negb (get_bit (allocated S alloc) n)) eqn:H_allocated; [discriminate|].
  
  injection H_dealloc as H_new_alloc_eq.
  
  assert (H_idx_eq: n = idx).
  {
    injection H_idx as H_idx_eq.
    exact H_idx_eq.
  }
  
  rewrite <- H_idx_eq.
  rewrite <- H_new_alloc_eq.
  simpl.
  
  assert (H_idx_bound: n < length (allocated S alloc)).
  {
    apply Bool.negb_false_iff in H_allocated.
    unfold get_bit in H_allocated.
    destruct (n <? length (allocated S alloc)) eqn:H_bound.
    - apply Nat.ltb_lt in H_bound. exact H_bound.
    - apply Nat.ltb_ge in H_bound.
      rewrite nth_overflow in H_allocated.
      + discriminate H_allocated.
      + exact H_bound.
  }
  
  apply get_bit_set_bit_same.
  exact H_idx_bound.
Qed.

Theorem allocate_frame_preserves_valid : 
  forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc idx,
  allocate_frame alloc = Some (frame, new_alloc) ->
  frame_idx alloc frame = Some idx ->
  get_bit (valid S alloc) idx = get_bit (valid S new_alloc) idx.
Proof.
  intros S alloc frame new_alloc idx H_alloc H_idx.
  unfold allocate_frame in H_alloc.
  destruct (first_one_from_zero (available alloc)) eqn:H_first; [|discriminate].
  destruct (frame_at_idx alloc n) eqn:H_frame; [|discriminate].
  injection H_alloc as H_frame_eq H_alloc_eq.
  subst frame new_alloc.
  simpl.
  reflexivity.
Qed.

(** A frame cannot be allocated twice without being deallocated *)
Theorem no_double_allocation : 
  forall {S : PageSize} (alloc : BitmapAllocator S) (f : PhysFrame S) (returned_frame : PhysFrame S) (new_alloc : BitmapAllocator S) (idx : nat),
  frame_idx alloc f = Some idx ->
  get_bit (allocated S alloc) idx = true ->
  allocate_frame alloc = Some (returned_frame, new_alloc) ->
  f <> returned_frame.
Proof.
  intros S alloc f returned_frame new_alloc idx H_f_idx H_f_bit_allocated H_alloc_result.
  intro H_eq.

  assert (H_returned_not_allocated: exists idx_ret, 
    frame_idx alloc returned_frame = Some idx_ret /\
    get_bit (valid S alloc) idx_ret = true /\
    get_bit (allocated S alloc) idx_ret = false).
  {
    apply frame_allocation_valid_unallocated with (new_alloc := new_alloc).
    exact H_alloc_result.
  }
  
  destruct H_returned_not_allocated as [idx_ret [H_ret_idx [H_ret_valid H_ret_not_allocated]]].

  assert (H_idx_eq: idx = idx_ret).
  {
    rewrite H_eq in H_f_idx.
    assert (H_same_idx: frame_idx alloc returned_frame = Some idx).
    { exact H_f_idx. }
    rewrite H_ret_idx in H_same_idx.
    injection H_same_idx as H_eq_idx.
    symmetry. exact H_eq_idx.
  }

  rewrite H_idx_eq in H_f_bit_allocated.
  rewrite H_f_bit_allocated in H_ret_not_allocated.
  discriminate H_ret_not_allocated.
Qed.

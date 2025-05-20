Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FSetList.
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
  
Admitted.

(** After deallocating a frame, the number of allocated frames decreases by 1 *)
Theorem deallocate_frame_decreases_count : forall {S : PageSize} (alloc : BitmapAllocator S) frame new_alloc,
  deallocate_frame alloc frame = Some new_alloc ->
  count_ones (allocated S new_alloc) = count_ones (allocated S alloc) - 1.
Proof.
  
Admitted.

(** A frame cannot be allocated twice without being deallocated *)
Theorem no_double_allocation : forall {S : PageSize} (alloc : BitmapAllocator S) frame1 new_alloc1 frame2 new_alloc2,
  allocate_frame alloc = Some (frame1, new_alloc1) ->
  allocate_frame new_alloc1 = Some (frame2, new_alloc2) ->
  frame1 <> frame2.
Proof.
  
Admitted.

(** * Usage *)

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


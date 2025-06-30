Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
From XY Require Import PhysicalMemory.
From XY Require Import BitArr.

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
Require Import Coq.ZArith.ZArith.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.

Local Open Scope uint63_scope.

(** * BitmapAllocator *)

Record BitmapAllocator (S : PageSize) (N : nat) := mkBitmapAllocator {
  allocated : BitArray N; (* Tracks allocated frames *)
  valid : BitArray N;     (* Tracks valid frames *)
  range : PhysFrameRange S;
}.

(** A frame index is within the allocator's range *)
Definition frame_idx_valid {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (idx : nat) : Prop :=
  idx < n * u64_bits.

(** * Well-formedness Predicate *)

(** An allocator is well-formed if allocated frames are always valid *)
Definition allocator_wf {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) : Prop :=
  forall idx : nat, 
    idx < n * u64_bits-> 
    get_bit (allocated S n alloc) idx = true -> 
    get_bit (valid S n alloc) idx = true.

(** Convert frame to index within the allocator's range *)
Definition frame_to_idx {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (frame : PhysFrame S) : option nat :=
  let frame_addr := start_address S frame in
  let range_start := start_address S (start_frame S (range S n alloc)) in
  let range_end := start_address S (end_frame S (range S n alloc)) in
  if (range_start <=? frame_addr) && (frame_addr <? range_end) then
    let offset := frame_addr - range_start in
    let idx := (offset / size S) in
    let ret := to_nat idx in
    Some ret 
  else None.

Search "mod_0_r".
Compute wB.
Compute of_Z wB mod (size (mkPageSize Page4KB)) .

Lemma add_mod : forall a b c : int, (a + b) mod c = ((a mod c) + (b mod c)) mod c.
Proof.
  intros a b c.
  destruct (eqs c 0) as [Hc_zero | Hc_nonzero].
  - subst c.
    apply to_Z_inj.
    repeat rewrite mod_spec.
    repeat rewrite add_spec.
    repeat rewrite mod_spec.
    rewrite to_Z_0.
    repeat rewrite Zmod_0_r.
    reflexivity.
  - apply to_Z_inj.
    repeat rewrite mod_spec.
    repeat rewrite add_spec.
    repeat rewrite mod_spec.
    admit.
    
Admitted.

(** Convert index to frame within the allocator's range *)
Program Definition idx_to_frame {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (idx : nat) : option (PhysFrame S) :=
  let frame_idx_u64 := of_nat idx in
  let frame_addr := start_address S (start_frame S (range S n alloc)) + (frame_idx_u64 * size S) in
  let range_end := start_address S (end_frame S (range S n alloc)) in
  if frame_addr <? range_end then
    let candidate_frame := mkPhysFrame S frame_addr _ in
    Some candidate_frame
  else 
    None.
Next Obligation.
  intros.
  set (start_addr := start_address S (start_frame S (range S n alloc))).
  
  destruct (start_frame S (range S n alloc)) as [start_addr' align_proof].
  simpl in start_addr.
  
  assert (start_addr mod (size S) = 0) as Hstart by exact align_proof.
  
  assert ((frame_idx_u64 * size S) mod (size S) = 0) as Hoffset.
  {
    repeat apply to_Z_inj.
    
    rewrite mod_spec.
    
    rewrite mul_spec.
    admit. }
  
  apply to_Z_inj.
  rewrite mod_spec.
  
  assert (to_Z (start_addr mod (size S)) = to_Z start_addr mod to_Z (size S))%Z.
  { rewrite mod_spec. reflexivity. }
  rewrite Hstart in H. simpl in H.
  
  assert (to_Z ((frame_idx_u64 * size S) mod (size S)) = to_Z (frame_idx_u64 * size S) mod to_Z (size S))%Z.
  { rewrite mod_spec. reflexivity. }
  rewrite Hoffset in H0. simpl in H0.
  
  admit.
Admitted.

Search (Z.modulo 0 _).
(** * Core Operations *)

(** Get available frames (valid AND not allocated) *)
Definition get_available {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) : BitArray n :=
  bitand (valid S n alloc) (bitnot (allocated S n alloc)).

(** Allocate a single frame *)
Definition allocate_frame {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) :
                          option (PhysFrame S * BitmapAllocator S n) :=
  match first_one_from_zero (get_available alloc) with
  | Some idx =>
      match idx_to_frame alloc idx with
      | Some frame =>
          let new_allocated := set_bit (allocated S n alloc) idx true in
          let new_alloc := mkBitmapAllocator S n new_allocated (valid S n alloc)
                                            (range S n alloc) in
          Some (frame, new_alloc)
      | None => None
      end
  | None => None  (* No available frames *)
  end.

(** Deallocate a frame *)
Definition deallocate_frame {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
                            (frame : PhysFrame S) :
                            option (BitmapAllocator S n) :=
  match frame_to_idx alloc frame with
  | Some idx =>
      (* Check that frame is valid and currently allocated *)
      if get_bit (valid S n alloc) idx && get_bit (allocated S n alloc) idx then
        let new_allocated := set_bit (allocated S n alloc) idx false in
        Some (mkBitmapAllocator S n new_allocated (valid S n alloc)
                                (range S n alloc))
      else None  (* Frame not valid or not allocated *)
  | None => None  (* Frame outside our range *)
  end.

(** * Utility Functions *)

(** Count valid frames *)
Definition num_valid {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) : nat :=
  count_ones (valid S n alloc).

(** Count allocated frames *)
Definition num_allocated {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) : nat :=
  count_ones (allocated S n alloc).

(** Count available frames *)
Definition num_available {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) : nat :=
  count_ones (get_available alloc).

(** Check if a specific frame is allocated *)
Definition is_frame_allocated {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
                              (frame : PhysFrame S) : bool :=
  match frame_to_idx alloc frame with
  | Some idx => get_bit (allocated S n alloc) idx
  | None => false
  end.

(** Check if a specific frame is valid *)
Definition is_frame_valid {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) 
                          (frame : PhysFrame S) : bool :=
  match frame_to_idx alloc frame with
  | Some idx => get_bit (valid S n alloc) idx
  | None => false
  end.
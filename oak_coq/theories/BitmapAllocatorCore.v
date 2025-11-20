Require Import Coq.ZArith.ZArith.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.
From OC Require Import MemoryModel.


Local Open Scope uint63_scope.

Notation "'let*' x ':=' e1 'in' e2" :=
  (match e1 with
   | Some x => e2
   | None => None
   end)
  (at level 61, x pattern, e1 at next level, right associativity).

Notation "'let*' ( x , y ) ':=' e1 'in' e2" :=
  (match e1 with
   | Some (x, y) => e2
   | None => None
   end)
  (at level 61, x pattern, y pattern, e1 at next level, right associativity).


Notation "'return' e" := (Some e) (at level 60).

(** A frame index is within the allocator's range *)
(* Definition frame_idx_valid {S : PageSize} {n : nat} (alloc : BitmapAllocator S n) (idx : nat) : Prop :=
  idx < n * u64_bits. *)

(** Well-formedness predicate for allocator state *)
Definition allocator_wf {S : PageSize} {n : nat} 
  (allocated valid : BitArray n) : Prop :=
  forall idx, 
    (Uint63.to_nat idx) < n * u64_bits -> 
    get_bit allocated idx = true -> 
    get_bit valid idx = true.


(** Get available frames (valid AND not allocated) *)
Definition get_available {n : nat} (allocated valid : BitArray n) : BitArray n :=
  bitand valid (bitnot allocated).

(** Translate: 
 fn frame(&self, frame_idx: usize) -> Option<PhysFrame<S>> {
        if self.range.end < self.range.start + frame_idx as u64 {
            None
        } else {
            Some(self.range.start + frame_idx as u64)
        }
    } *)
Program Definition frame {S : PageSize} {n : nat}
  (p : program_state) (alloc_addr : addr) (frame_idx : Uint63.int) : option (PhysFrame S) :=
  
  let* alloc := @read_allocator S n p alloc_addr in
  
  if start_address S (end_frame S (range alloc)) <? start_address S (start_frame S (range alloc)) + (frame_idx * size S) then
    None
  else 
    return (mkPhysFrame S ((start_address S (start_frame S (range alloc))) + (frame_idx * size S)) _).

Next Obligation.
Admitted.

(** Translate:
fn frame_idx(&self, frame: PhysFrame<S>) -> Option<usize> {
        if frame < self.range.start || frame > self.range.end {
            None
        } else {
            Some(
                ((frame.start_address().as_u64() - self.range.start.start_address().as_u64())
                    / S::SIZE) as usize,
            )
        }
    } *)
Definition frame_idx {S : PageSize} {n : nat}
  (p : program_state) (alloc_addr : addr) (frame : PhysFrame S) : option Uint63.int :=
  
  let* alloc := @read_allocator S n p alloc_addr in
  
  if (start_address S frame <? start_address S (start_frame S (range alloc))) 
  || (start_address S (end_frame S (range alloc)) <? start_address S frame) then
    None
  else 
    return ((start_address S frame - start_address S (start_frame S (range alloc))) 
    / size S).


Definition fill {n : nat} (bits : BitArray n) (start_idx end_idx : nat) (value : bool) : BitArray n :=
  fold_left 
    (fun acc idx => set_bit acc idx value) 
    (map (fun n => of_Z (Z.of_nat n)) (seq start_idx (if Nat.leb start_idx end_idx then S (end_idx - start_idx) else 0)))
    bits.

(** Translate:
pub fn mark_valid(&mut self, range: PhysFrameRange<S>, valid: bool) {
        if let (Some(start), Some(end)) = (self.frame_idx(range.start), self.frame_idx(range.end)) {
            self.valid.get_mut(start..end).unwrap().fill(valid);
        } else {
            panic!(
                "Can't mark validity for frame range that's outside our range; our range: {:?}, frame range: {:?}",
                self.range, range
            );
        }
    } *)
Definition mark_valid {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) 
  (frame_range : PhysFrameRange S) (is_valid : bool) : option program_state :=
  let* allocator := @read_allocator S n p alloc_addr in
  
  let* start_idx := @frame_idx S n p alloc_addr (start_frame S frame_range) in
  let* end_idx := @frame_idx S n p alloc_addr (end_frame S frame_range) in
  
  let (p1, start_idx_addr) := alloc p (VUint63 start_idx) in
  let (p2, end_idx_addr) := alloc p1 (VUint63 end_idx) in
  
  let new_valid := fill allocator.(valid) (Z.to_nat (to_Z start_idx)) (Z.to_nat (to_Z end_idx)) is_valid in
  let* p3 := @update_allocator_valid S n p2 alloc_addr new_valid in
  let* p4 := dealloc p3 end_idx_addr in
  let* p5 := dealloc p4 start_idx_addr in

  return p5.


(** Translate:
unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for BitmapAllocator<S, N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?;
        self.allocated.set(frame_idx, true);
        self.frame(frame_idx)
    }
}*)
Definition allocate_frame {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) : 
  option (PhysFrame S * program_state) :=
  let* allocator := @read_allocator S n p alloc_addr in

  let* frame_idx := first_one_from_zero (get_available (allocated allocator) (valid allocator)) in
  let (p1, frame_idx_addr) := alloc p (VUint63 frame_idx) in
  
  let* p2 := @update_allocator_allocated S n p1 alloc_addr (set_bit (allocated allocator) frame_idx true) in
  let* frame := @frame S n p alloc_addr frame_idx in

  let* p3 := dealloc p2 frame_idx_addr in
  return (frame, p3).

(** Translate:
unsafe fn deallocate_frame(&mut self, frame: PhysFrame<S>) {
        if let Some(frame_idx) = self.frame_idx(frame) {
            if !self.valid[frame_idx] {
                panic!("frame {:?} is not valid in this allocator", frame);
            }
            if !self.allocated[frame_idx] {
                panic!("frame {:?} was not allocated in this allocator", frame);
            }
            self.allocated.set(frame_idx, false);
        } else {
            panic!(
                "can't deallocate frame that's outside our range; our range: {:?}, frame: {:?}",
                self.range, frame
            );
        }
    } *)
Definition deallocate_frame {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) (frame : PhysFrame S) :
  option program_state :=
  let* allocator := @read_allocator S n p alloc_addr in
  
  let* frame_idx := @frame_idx S n p alloc_addr frame in
  let (p1, frame_idx_addr) := alloc p (VUint63 frame_idx) in
  
  if negb (get_bit (valid allocator) frame_idx) then
    None
  else if negb (get_bit (allocated allocator) frame_idx) then
    None
  else
    let* p2 := @update_allocator_allocated S n p1 alloc_addr (set_bit (allocated allocator) frame_idx false) in
    let* p3 := dealloc p2 frame_idx_addr in
    return p3.


(** * Utility Functions *)

(** Count valid frames *)
Definition num_valid {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) : option nat :=
  match @read_allocator S n p alloc_addr with
  | Some alloc => Some (@count_ones n (valid alloc))
  | None => None
  end.

(** Count allocated frames *)
Definition num_allocated {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) : option nat :=
  match @read_allocator S n p alloc_addr with
  | Some alloc => Some (@count_ones n (allocated alloc))
  | None => None
  end.

(** Count available frames *)
Definition num_available {S : PageSize} {n : nat} 
  (p : program_state) (alloc_addr : addr) : option nat :=
  match @read_allocator S n p alloc_addr with
  | Some alloc => Some (@count_ones n (get_available (allocated alloc) (valid alloc)))
  | None => None
  end.

(** Initialize allocator with valid regions *)
Definition init_allocator {S : PageSize} {n : nat}
  (p : program_state) (alloc_addr : addr) 
  (ranges_with_validity : list (PhysFrameRange S * bool)) : option program_state :=
  fold_left (fun acc_p range_validity => 
    match acc_p with
    | Some p' => @mark_valid S n p' alloc_addr (fst range_validity) (snd range_validity)
    | None => None
    end) ranges_with_validity (Some p).
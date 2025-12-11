Require Import Coq.ZArith.ZArith.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.
From OC Require Import VariableModel.

Local Open Scope uint63_scope.

Notation "'let*' x ':=' e1 'in' e2" :=
  (match e1 with
   | Some x => e2
   | None => None
   end)
  (at level 62, x pattern, e1 at next level, right associativity).

Notation "'let*' ( x , y ) ':=' e1 'in' e2" :=
  (match e1 with
   | Some (x, y) => e2
   | None => None
   end)
  (at level 62, x pattern, y pattern, e1 at next level, right associativity).

Notation "'return' e" := (Some e) (at level 60).

(** Well-formedness predicate for allocator state *)
Definition allocator_wf {S : PageSize} {n : nat} 
  (alloc : BitmapAllocator S n) : Prop :=
  forall idx, 
    (Uint63.to_nat idx) < n * u64_bits -> 
    get_bit (allocated alloc) idx = true -> 
    get_bit (valid alloc) idx = true.

(** Get available frames (valid AND not allocated) *)
Definition get_available {n : nat} (allocated valid : BitArray n) : BitArray n :=
  bitand valid (bitnot allocated).

(** Read allocator from a variable *)
Definition read_allocator {S : PageSize} {n : nat} 
  (p : prog_state) (var : var_name) : option (BitmapAllocator S n) :=
  match read_var p var with
  | Some (@VAllocator S' n' alloc) => 
      match PageSize_eq_dec S S', Nat.eq_dec n n' with
      | left Seq, left neq => 
          let alloc' := eq_rect n' (fun n => BitmapAllocator S' n) alloc n (eq_sym neq) in
          let alloc'' := eq_rect S' (fun S => BitmapAllocator S n) alloc' S (eq_sym Seq) in
          Some alloc''
      | _, _ => None
      end
  | _ => None
  end.

(** Update allocator's allocated bitmap *)
Definition update_allocator_allocated {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) (new_allocated : BitArray n) 
  : option prog_state :=
  let* alloc := @read_allocator S n p var in
  let new_alloc := mkBitmapAllocator new_allocated (valid alloc) (range alloc) in
  write_var p var (@VAllocator S n new_alloc).

(** Update allocator's valid bitmap *)
Definition update_allocator_valid {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) (new_valid : BitArray n) 
  : option prog_state :=
  let* alloc := @read_allocator S n p var in
  let new_alloc := mkBitmapAllocator (allocated alloc) new_valid (range alloc) in
  write_var p var (@VAllocator S n new_alloc).

(** Create a new allocator - returns variable name to use *)
Definition new_allocator {S : PageSize} (n : nat) 
  (p : prog_state) (var : var_name) (r : PhysFrameRange S) (lt_end : nat) 
  : option (prog_state * addr) :=
  let alloc := mkBitmapAllocator (make_bitarray n) (make_bitarray n) r in
  let_mut_owned p var (@VAllocator S n alloc) lt_end.

(** Translate: 
 fn frame(&self, frame_idx: usize) -> Option<PhysFrame<S>> {
        if self.range.end < self.range.start + frame_idx as u64 {
            None
        } else {
            Some(self.range.start + frame_idx as u64)
        }
    } *)
Program Definition frame {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) (frame_idx : Uint63.int) 
  : option (PhysFrame S) :=
  let* alloc := @read_allocator S n p var in
  let frame_range := range alloc in
  let start_addr := start_address S (start_frame S frame_range) in
  let end_addr := start_address S (end_frame S frame_range) in
  let computed_addr := start_addr + (frame_idx * size S) in
  
  if end_addr <? computed_addr then
    None
  else 
    return (mkPhysFrame S computed_addr _).
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
  (p : prog_state) (var : var_name) (frame : PhysFrame S) 
  : option Uint63.int :=
  let* alloc := @read_allocator S n p var in
  let frame_range := range alloc in
  let start_addr := start_address S (start_frame S frame_range) in
  let end_addr := start_address S (end_frame S frame_range) in
  let frame_addr := start_address S frame in
  
  if (frame_addr <? start_addr) || (end_addr <? frame_addr) then
    None
  else 
    return ((frame_addr - start_addr) / size S).

(** Helper to set multiple bits in a range *)
Definition fill {n : nat} (bits : BitArray n) (start_idx end_idx : nat) (value : bool) 
  : BitArray n :=
  fold_left 
    (fun acc idx => set_bit acc idx value) 
    (map (fun n => of_Z (Z.of_nat n)) 
         (seq start_idx (if Nat.leb start_idx end_idx 
                        then S (end_idx - start_idx) 
                        else 0)))
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
  (p : prog_state) (var : var_name) 
  (frame_range : PhysFrameRange S) (is_valid : bool) 
  : option prog_state :=
  let* allocator := @read_allocator S n p var in
  
  let* start_idx := @frame_idx S n p var (start_frame S frame_range) in
  let* end_idx := @frame_idx S n p var (end_frame S frame_range) in
  
  let new_valid := fill (valid allocator) 
                       (Z.to_nat (to_Z start_idx)) 
                       (Z.to_nat (to_Z end_idx)) 
                       is_valid in
  
  @update_allocator_valid S n p var new_valid.

(** Translate:
unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for BitmapAllocator<S, N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?;
        self.allocated.set(frame_idx, true);
        self.frame(frame_idx)
    }
}*)
Definition allocate_frame {S : PageSize} {n : nat} 
  (p : prog_state) (var : var_name) 
  : option (PhysFrame S * prog_state) :=
  let* allocator := @read_allocator S n p var in

  let available := get_available (allocated allocator) (valid allocator) in
  let* frame_idx := first_one_from_zero available in
  
  let new_allocated := set_bit (allocated allocator) frame_idx true in
  let* p' := @update_allocator_allocated S n p var new_allocated in
  
  let* frame := @frame S n p' var frame_idx in
  
  return (frame, p').

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
  (p : prog_state) (var : var_name) (frame : PhysFrame S)
  : option prog_state :=
  let* allocator := @read_allocator S n p var in
  
  let* frame_idx := @frame_idx S n p var frame in
  
  if negb (get_bit (valid allocator) frame_idx) then
    None
  else if negb (get_bit (allocated allocator) frame_idx) then
    None
  else
    let new_allocated := set_bit (allocated allocator) frame_idx false in
    @update_allocator_allocated S n p var new_allocated.

(** Initialize allocator with valid regions *)
Definition init_allocator {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) 
  (ranges_with_validity : list (PhysFrameRange S * bool)) 
  : option prog_state :=
  fold_left (fun acc_p range_validity => 
    match acc_p with
    | Some p' => @mark_valid S n p' var 
                            (fst range_validity) 
                            (snd range_validity)
    | None => None
    end) 
  ranges_with_validity 
  (Some p).

(** Helper to check if frame is valid *)
Definition is_frame_valid {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) (frame : PhysFrame S) 
  : option bool :=
  let* allocator := @read_allocator S n p var in
  let* idx := @frame_idx S n p var frame in
  return (get_bit (valid allocator) idx).

(** Helper to check if frame is allocated *)
Definition is_frame_allocated {S : PageSize} {n : nat}
  (p : prog_state) (var : var_name) (frame : PhysFrame S) 
  : option bool :=
  let* allocator := @read_allocator S n p var in
  let* idx := @frame_idx S n p var frame in
  return (get_bit (allocated allocator) idx).

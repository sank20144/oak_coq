Require Import Coq.ZArith.ZArith.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.
From OC Require Import VariableModel.
From OC Require Import BitArrLemmas.

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

Inductive Result (A : Type) : Type :=
  | Ok : A -> Result A
  | Err : Result A
  | Panic : Result A.

Arguments Ok {A}.
Arguments Err {A}.
Arguments Panic {A}.

(** Well-formedness predicate for allocator state *)
Definition allocator_wf {S : PageSize} {n : Uint63.int} 
  (alloc : BitmapAllocator S n) : Prop :=
  forall idx, 
    (Uint63.to_nat idx) < (to_nat n) * u64_bits -> 
    get_bit (allocated alloc) idx = true -> 
    get_bit (valid alloc) idx = true.

(** Get available frames (valid AND not allocated) *)
Definition get_available {n : Uint63.int} (allocated valid : BitArray n) : BitArray n :=
  bitand valid (bitnot allocated).

(** Read allocator from a variable *)
Definition read_allocator {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (var : var_name) : option (BitmapAllocator S n) :=
  match read_var p var with
  | Some (@VAllocator S' n' alloc) => 
      match PageSize_eq_dec S S' with
      | left Seq => 
          match Uint63.eqb n n' as b return (b = Uint63.eqb n n' -> _) with
          | true => fun (Heq : true = Uint63.eqb n n') =>
              let alloc' := eq_rect n' (fun n => BitmapAllocator S' n) alloc n (eq_sym (proj1 (Uint63.eqb_spec n n') (eq_sym Heq))) in
              let alloc'' := eq_rect S' (fun S => BitmapAllocator S n) alloc' S (eq_sym Seq) in
              Some alloc''
          | false => fun _ => None
          end eq_refl
      | right _ => None
      end
  | _ => None
  end.

Definition read_mut_allocator {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (borrow_end : nat)
  : option (prog_state * var_name * BitmapAllocator S n) :=
  let ref_var := self ++ "_mut_ref" in
  match let_mut_ref p ref_var self borrow_end with
  | None => None
  | Some p_ref =>
      match @read_allocator S n p_ref ref_var with
      | None => None
      | Some alloc => Some (p_ref, ref_var, alloc)
      end
  end.

Definition read_shared_allocator {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (borrow_end : nat)
  : option (prog_state * var_name * BitmapAllocator S n) :=
  let ref_var := self ++ "_ref" in
  match let_shared_ref p ref_var self borrow_end with
  | None => None
  | Some p_ref =>
      match @read_allocator S n p_ref ref_var with
      | None => None
      | Some alloc => Some (p_ref, ref_var, alloc)
      end
  end.

Notation "'read_mut_alloc' [ S , n ] self 'as' ref 'in' body" :=
  (match @read_mut_allocator S n _ self _ with
   | None => Panic
   | Some (p_ref, ref, alloc) => body
   end)
  (at level 62, self at level 0, ref at level 0, body at next level).

Notation "'read_shared_alloc' [ S , n ] self 'as' ref 'in' body" :=
  (match @read_shared_allocator S n _ self _ with
   | None => Panic
   | Some (p_ref, ref, alloc) => body
   end)
  (at level 62, self at level 0, ref at level 0, body at next level).

Notation "'read_mut_alloc' [ S , n ] self 'as' '(' p ',' ref ',' alloc ')' 'in' body" :=
  (match @read_mut_allocator S n _ self _ with
   | None => Panic
   | Some (p, ref, alloc) => body
   end)
  (at level 62, self at level 0, p pattern, ref pattern, alloc pattern, body at next level).

Notation "'read_shared_alloc' [ S , n ] self 'as' '(' p ',' ref ',' alloc ')' 'in' body" :=
  (match @read_shared_allocator S n _ self _ with
   | None => Panic
   | Some (p, ref, alloc) => body
   end)
  (at level 62, self at level 0, p pattern, ref pattern, alloc pattern, body at next level).

Notation "'read_shared_alloc' [ S , n ] 'from' p 'at' self 'for' lt 'as' '(' p' ',' ref ',' alloc ')' 'in' body" :=
  (match @read_shared_allocator S n p self lt with
   | None => Panic
   | Some (p', ref, alloc) => body
   end)
  (at level 62, p at level 0, self at level 0, lt at level 0, 
   p' pattern, ref pattern, alloc pattern, body at next level).

Notation "'read_mut_alloc' [ S , n ] 'from' p 'at' self 'for' lt 'as' '(' p' ',' ref ',' alloc ')' 'in' body" :=
  (match @read_mut_allocator S n p self lt with
   | None => Panic
   | Some (p', ref, alloc) => body
   end)
  (at level 62, p at level 0, self at level 0, lt at level 0, 
   p' pattern, ref pattern, alloc pattern, body at next level).


Definition write_and_drop {S : PageSize} {n : Uint63.int}
  (p : prog_state) (ref_var : var_name) (alloc : BitmapAllocator S n)
  : Result prog_state :=
  match write_var p ref_var (@VAllocator S n alloc) with
  | Some p' =>
      match drop_var p' ref_var with
      | Some p_final => Ok p_final
      | None => Err
      end
  | None => Err
  end.

Definition drop_and_return {S : PageSize} {n : Uint63.int} {A : Type}
  (p : prog_state) (ref_var : var_name) (result : Result A)
  : Result A :=
  match drop_var p ref_var with
  | Some _ => result
  | None => Panic
  end.

Notation "'let!' x ':=' e1 'in' e2" :=
  (match e1 with
   | Ok x => e2
   | Err => Err
   | Panic => Panic
   end)
  (at level 62, x pattern, e1 at next level, right associativity).

Notation "'let!?' [ S , n , A ] x 'with' p_ref 'and' ref_var ':=' e1 'in' e2" :=
  (match e1 with
   | Some x => e2
   | None => 
       let p_ref := step_forward p_ref in
       @drop_and_return S n A p_ref ref_var Err
   end)
  (at level 62, S at level 0, n at level 0, A at level 0, x pattern, 
   p_ref at level 0, ref_var at level 0, e1 at next level, right associativity).

(** Create a new allocator*)
Definition new_allocator {S : PageSize} (n : Uint63.int) 
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
Program Definition frame {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (frame_idx : Uint63.int)
  : Result (PhysFrame S) :=
  read_shared_alloc [S, n] self as (p_ref, ref_var, alloc) in
    if start_address S (end_frame S (range alloc)) <? 
       start_address S (start_frame S (range alloc)) + (frame_idx * size S) then
      let p_ref := step_forward p_ref in
      @drop_and_return S n (PhysFrame S) p_ref ref_var Err
    else
      let p_ref := step_forward p_ref in
      @drop_and_return S n (PhysFrame S) p_ref ref_var (Ok (mkPhysFrame S (start_address S (start_frame S (range alloc)) + (frame_idx * size S)) _)).
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
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

Definition frame_idx {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (frame : PhysFrame S)
  : Result Uint63.int :=
  read_shared_alloc [S, n] from p at self for 5 as (p_ref, ref_var, alloc) in
    if (start_address S frame <? start_address S (start_frame S (range alloc))) || 
       (start_address S (end_frame S (range alloc)) <? start_address S frame) then
      let p_ref := step_forward p_ref in
      @drop_and_return S n Uint63.int p_ref ref_var Err
    else 
      let p_ref := step_forward p_ref in
      @drop_and_return S n Uint63.int p_ref ref_var 
        (Ok ((start_address S frame - start_address S (start_frame S (range alloc))) / size S)).

(** Helper to set multiple bits in a range *)
Definition fill {n : Uint63.int} (bits : BitArray n) (start_idx end_idx : nat) (value : bool) 
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
Definition mark_valid {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (self : var_name) 
  (frame_range : PhysFrameRange S) (is_valid : bool)
  : Result prog_state :=
  read_mut_alloc [S, n] from p at self for 2 as (p_ref, ref_var, alloc) in
    match (@frame_idx S n p_ref ref_var (start_frame S frame_range),
           @frame_idx S n p_ref ref_var (end_frame S frame_range)) with
    | (Ok start_idx, Ok end_idx) =>
        let p_ref := step_forward p_ref in
        let new_valid := @fill n (@valid S n alloc)
                             (Z.to_nat (to_Z start_idx)) 
                             (Z.to_nat (to_Z end_idx)) 
                             is_valid in
        let new_alloc := mkBitmapAllocator (@allocated S n alloc) new_valid (@range S n alloc) in
        let p_ref := step_forward p_ref in
        write_and_drop p_ref ref_var new_alloc
    | _ => Panic
    end.

(** Translate:
unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for BitmapAllocator<S, N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?;
        self.allocated.set(frame_idx, true);
        self.frame(frame_idx)
    }
}*)
Definition allocate_frame {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (self : var_name)
  : Result (PhysFrame S * prog_state) :=
  read_mut_alloc [S, n] from p at self for 4 as (p_ref, ref_var, allocator) in
    (* let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?; *)
    let!? [S, n, (PhysFrame S * prog_state)] frame_idx with p_ref and ref_var := first_one_from_zero (get_available (allocated allocator) (valid allocator)) in
    let p_ref := step_forward p_ref in
    (* self.allocated.set(frame_idx, true); *)
    let new_alloc := mkBitmapAllocator (set_bit (allocated allocator) frame_idx true) (valid allocator) (range allocator) in
    let p_ref := step_forward p_ref in
    let! p' := write_and_drop p_ref ref_var new_alloc in
    (* self.frame(frame_idx) *)
    let! frame_result := @frame S n p' self frame_idx in
    Ok (frame_result, p').

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
Definition deallocate_frame {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (self : var_name) (frame : PhysFrame S)
  : Result prog_state :=
  read_mut_alloc [S, n] from p at self for 4 as (p_ref, ref_var, allocator) in
    (* if let Some(frame_idx) = self.frame_idx(frame) *)
    let! frame_idx := @frame_idx S n p_ref ref_var frame in
    let p_ref := step_forward p_ref in
    (* if !self.valid[frame_idx] { panic!(...) } *)
    match get_bit (valid allocator) frame_idx with
    | false => Panic
    | true =>
        let p_ref := step_forward p_ref in
        (* if !self.allocated[frame_idx] { panic!(...) } *)
        match get_bit (allocated allocator) frame_idx with
        | false => Panic
        | true =>
            (* self.allocated.set(frame_idx, false); *)
            let p_ref := step_forward p_ref in
            let new_alloc := mkBitmapAllocator (set_bit (allocated allocator) frame_idx false) (valid allocator) (range allocator) in
            let p_ref := step_forward p_ref in
            write_and_drop p_ref ref_var new_alloc
        end
    end.

(** Initialize allocator with valid regions *)
Definition init_allocator {S : PageSize} {n : Uint63.int}
  (p : prog_state) (var : var_name) 
  (ranges_with_validity : list (PhysFrameRange S * bool)) 
  : option prog_state :=
  fold_left (fun acc_p range_validity => 
    match acc_p with
    | Some p' => 
        match @mark_valid S n p' var 
                            (fst range_validity) 
                            (snd range_validity) with
        | Ok p'' => Some p''
        | _ => None
        end
    | None => None
    end) 
  ranges_with_validity 
  (Some p).



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
From OC Require Export BitmapAllocatorModelLemmas.

Local Open Scope string_scope.

Section RefLemmas.
Context {S : PageSize} {n : Uint63.int}.


(** frame_idx returns the same index that was used to create a frame via the frame function *)
Lemma frame_idx_of_frame
  (p : prog_state) (self : var_name) (idx : Uint63.int) (f : PhysFrame S) :
  @frame S n p self idx = Ok f ->
  @frame_idx S n p self f = Ok idx.
Proof.
Admitted. 

(** frame_idx depends only on the range, not on the prog_state details *)
Lemma frame_idx_depends_on_range
  (p1 p2 : prog_state) (v1 v2 : var_name) (f : PhysFrame S)
  (alloc1 alloc2 : BitmapAllocator S n) :
  read_allocator p1 v1 = Some alloc1 ->
  read_allocator p2 v2 = Some alloc2 ->
  range alloc1 = range alloc2 ->
  (exists p1_ref v1_ref, @read_shared_allocator S n p1 v1 2 = Some (p1_ref, v1_ref, alloc1) /\
                       exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin) ->
  (exists p2_ref v2_ref, @read_shared_allocator S n p2 v2 2 = Some (p2_ref, v2_ref, alloc2) /\
                       exists p2_fin, drop_var (step_forward p2_ref) v2_ref = Some p2_fin) ->
  @frame_idx S n p1 v1 f = @frame_idx S n p2 v2 f.
Proof.
Admitted.

Lemma var_lookup_var_remove_diff (vars : var_env) (v1 v2 : var_name) :
  v1 <> v2 ->
  var_lookup (var_remove vars v1) v2 = var_lookup vars v2.
Proof.
Admitted.

(** write_and_drop preserves step counter with offset *)
Lemma write_and_drop_preserves_step
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  ps_current_step p' = ps_current_step p.
Proof.
Admitted.


(** ref_var created by read_mut_allocator is different from self *)
Lemma read_mut_allocator_ref_var_diff
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  ref_var = (self ++ "_mut_ref")%string.
Proof.
Admitted.

(** After let_mut_ref succeeds from a state where read_allocator succeeds,
    read_allocator through the new mutable reference also succeeds *)
Lemma let_mut_ref_preserves_read_allocator
  (p p' : prog_state) (self ref_var : var_name) (borrow_end : nat)
  (alloc : BitmapAllocator S n) :
  let_mut_ref p ref_var self borrow_end = Some p' ->
  read_allocator p self = Some alloc ->
  ps_current_step p < borrow_end ->
  read_allocator p' ref_var = Some alloc.
Proof.
Admitted.

Lemma read_mut_allocator_ref_droppable
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref < ps_current_step p + duration ->
  exists p', drop_var (step_forward p_ref) ref_var = Some p'.
Proof.
Admitted.

Lemma read_mut_allocator_preserves_step
  (p p_ref : prog_state) (self ref_var : var_name) (borrow_end : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self borrow_end = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref = ps_current_step p.
Proof.
Admitted.

(** After write_and_drop succeeds, the original variable is still accessible with LocOwned *)
Lemma write_and_drop_preserves_var_ownership
  (p p' : prog_state) (ref_var self : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) (lt : lifetime) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  write_and_drop p ref_var new_alloc = Ok p' ->
  ref_var <> self ->
  var_lookup (ps_vars p') self = Some (VarMutOwned a lt).
Proof.
Admitted.

(** After write_and_drop succeeds for a mutable reference, the heap location returns to LocOwned *)
Lemma write_and_drop_restores_loc_owned
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  (* If ref_var was a VarMutRef pointing to address a *)
  (exists lt, var_lookup (ps_vars p) ref_var = Some (VarMutRef a lt)) ->
  (* and it was the ONLY borrow *)
  (exists lt cell, heap_lookup (ps_heap p) a = Some (cell, LocMut [lt])) ->
  heap_lookup (ps_heap p') a = Some (mk_cell (VAllocator new_alloc), LocOwned).
Proof.
Admitted.

(** read_mut_allocator preserves the original variable *)
Lemma read_mut_allocator_preserves_original_var
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  var_lookup (ps_vars p_ref) self = Some (VarMutOwned a lt).
Proof.
Admitted.

Lemma read_shared_allocator_succeeds
  (p : prog_state) (self : var_name) (a : addr) (lt : lifetime) (m : mem_cell)
  (alloc : BitmapAllocator S n) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  lifetime_active p lt = true ->
  (ps_current_step p + 2 <= lt_end lt)%nat ->
  heap_lookup (ps_heap p) a = Some (m, LocOwned) ->
  read_allocator p self = Some alloc ->
  exists p_ref ref_var,
    @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc).
Proof.
Admitted.

Lemma drop_shared_ref_succeeds
  (p : prog_state) (v : var_name) (p_ref : prog_state) (v_ref : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc) ->
  exists p_fin, drop_var (step_forward p_ref) v_ref = Some p_fin.
Proof.
Admitted.

(** read_mut_allocator creates ref to same address as original variable *)
Lemma read_mut_allocator_same_addr
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  exists lt_ref, var_lookup (ps_vars p_ref) ref_var = Some (VarMutRef a lt_ref).
Proof.
Admitted.

(** Helper: read_mut_allocator results in a specific heap state *)
Lemma read_mut_allocator_heap_state
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  (exists m, heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->
  exists cell lt_ref, heap_lookup (ps_heap p_ref) a = Some (cell, LocMut [lt_ref]).
Proof.
Admitted.


(** Helper: read_allocator returns the exact allocator if types match *)
Lemma read_allocator_same 
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n) :
  read_var p v = Some (VAllocator alloc) ->
  read_allocator p v = Some alloc.
Proof.
Admitted.

(** read_mut_allocator gives consistent var and heap states *)
Lemma read_mut_allocator_ref_and_heap
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  (exists m, heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->
  exists lt_ref,
    var_lookup (ps_vars p_ref) ref_var = Some (VarMutRef a lt_ref) /\
    exists cell, heap_lookup (ps_heap p_ref) a = Some (cell, LocMut [lt_ref]).
Proof.
Admitted.

(** read_mut_allocator preserves the content of the allocator *)
Lemma read_mut_allocator_preserves_content
  (p : prog_state) (self : var_name) (borrow_end : nat) (alloc : BitmapAllocator S n) :
  borrow_end > 0 -> 
  read_allocator p self = Some alloc ->
  match read_mut_allocator p self borrow_end with
  | Some (p_ref, ref_var, alloc') => 
      allocated alloc = allocated alloc' /\
      valid alloc = valid alloc' /\
      range alloc = range alloc'
  | None => True
  end.
Proof.
Admitted.

(** frame only panics when read_shared_allocator fails *)
Lemma frame_panic_iff_read_shared_fails
  (p : prog_state) (self : var_name) (idx : Uint63.int) :
  @frame S n p self idx = Panic <->
  @read_shared_allocator S n p self 2 = None.
Proof.
Admitted.

(** The allocator after write_and_drop has the updated content *)
Lemma write_and_drop_allocator_content
  (p p' : prog_state) (ref_var self : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) (lt : lifetime) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  lifetime_active p lt = true ->
  (exists lt_ref, var_lookup (ps_vars p) ref_var = Some (VarMutRef a lt_ref) /\
                exists cell, heap_lookup (ps_heap p) a = Some (cell, LocMut [lt_ref])) ->
  ref_var <> self ->
  exists alloc', read_allocator p' self = Some alloc' /\
    allocated alloc' = allocated new_alloc /\
    valid alloc' = valid new_alloc /\
    range alloc' = range new_alloc.
Proof.
Admitted.

Lemma read_mut_allocator_setup
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) (m : mem_cell) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  heap_lookup (ps_heap p) a = Some (m, LocOwned) ->
  ref_var <> self
  /\ ps_current_step p_ref = ps_current_step p
  /\ var_lookup (ps_vars p_ref) self = Some (VarMutOwned a lt)
  /\ (exists lt_ref,
        var_lookup (ps_vars p_ref) ref_var = Some (VarMutRef a lt_ref) /\
        exists cell, heap_lookup (ps_heap p_ref) a = Some (cell, LocMut [lt_ref])).
Proof.
Admitted.

(** If read_shared_allocator succeeds, frame doesn't panic *)
Lemma frame_not_panic_when_read_shared_succeeds
  (p : prog_state) (self : var_name) (idx : Uint63.int)
  (p_ref : prog_state) (ref_var : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc) ->
  @frame S n p self idx <> Panic.
Proof.
Admitted.

(** If read_shared_allocator succeeds with proper preconditions, frame doesn't panic *)
Lemma frame_not_panic_when_accessible
  (p : prog_state) (self : var_name) (idx : Uint63.int)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) (m : mem_cell) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  read_allocator p self = Some alloc ->
  lifetime_active p lt = true ->
  ps_current_step p + 2 <= lt_end lt ->
  heap_lookup (ps_heap p) a = Some (m, LocOwned) ->
  @frame S n p self idx <> Panic.
Proof.
Admitted.


End RefLemmas.

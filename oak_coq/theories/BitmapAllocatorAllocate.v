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
From OC Require Export BitmapAllocatorRefLemmas.

Local Open Scope string_scope.

Section AllocateFrame.
Context {S : PageSize} {n : Uint63.int}.


(** If read_allocator and read_shared_allocator both succeed on the same variable,
    they return the same allocator. *)
Lemma read_shared_allocator_returns_same_alloc
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n)
  (p_ref : prog_state) (v_ref : var_name) (alloc' : BitmapAllocator S n) :
  read_allocator p v = Some alloc ->
  @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc') ->
  alloc' = alloc.
Proof.
Admitted.

Lemma read_shared_allocator_succeeds_from_mut_ref
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n) :
  read_allocator p v = Some alloc ->
  (exists (a: addr) (lt: lifetime) (lt_ref: lifetime), var_lookup (ps_vars p) v = Some (VarMutRef a lt_ref) /\
                lifetime_active p lt_ref = true /\
                ps_current_step p + 2 <= lt_end lt_ref /\
                exists (cell: mem_cell), heap_lookup (ps_heap p) a = Some (cell, LocMut [lt_ref]) /\
                lifetime_contained_in 
                  {| lt_id := ps_next_lifetime_id p; 
                     lt_start := ps_current_step p; 
                     lt_end := ps_current_step p + 2 |} lt_ref = true) ->
  (exists p_ref v_ref, @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc) /\
                       exists p_fin, drop_var (step_forward p_ref) v_ref = Some p_fin).
Proof.
Admitted.

(** frame_idx transfers between states with the same allocator range *)
Lemma frame_idx_transfer
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

(** If read_allocator succeeds and the variable conditions hold,
    read_shared_allocator also succeeds with the same allocator and
    the subsequent drop_var/step_forward succeeds. *)
Lemma read_shared_allocator_succeeds_from_alloc
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n) :
  read_allocator p v = Some alloc ->
  (exists a lt m, var_lookup (ps_vars p) v = Some (VarMutOwned a lt) /\
                lifetime_active p lt = true /\
                ps_current_step p + 2 <= lt_end lt /\
                heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->
  (exists p_ref v_ref, @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc) /\
                       exists p_fin, drop_var (step_forward p_ref) v_ref = Some p_fin).
Proof.
Admitted.

(** frame_idx only panics when read_shared_allocator fails *)
Lemma frame_idx_panic_iff_read_shared_fails
  (p : prog_state) (self : var_name) (frame : PhysFrame S) :
  @frame_idx S n p self frame = Panic <->
  @read_shared_allocator S n p self 2 = None.
Proof.
Admitted.

(** If read_shared_allocator succeeds, frame_idx doesn't panic *)
Lemma frame_idx_not_panic_when_read_shared_succeeds
  (p : prog_state) (self : var_name) (frame : PhysFrame S)
  (p_ref : prog_state) (ref_var : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc) ->
  @frame_idx S n p self frame <> Panic.
Proof.
Admitted.

(** Allocation returns a valid, previously unallocated frame *)
Theorem allocate_frame_correctness 
  (p : prog_state) (self : var_name) :

  (Z.of_nat (to_nat n * u64_bits) < wB)%Z ->

  (exists alloc, read_allocator p self = Some alloc /\ 
    @allocator_wf S n alloc) ->
  
  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                lifetime_active p lt = true /\
                ps_current_step p + 6 <= lt_end lt /\
                heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->
  match @allocate_frame S n p self with
  | Ok (frame, p') => 

      (exists alloc, read_allocator p self = Some alloc /\
        exists idx, @frame_idx S n p self frame = Ok idx /\
          get_bit (valid alloc) idx = true /\           
          get_bit (@allocated S n alloc) idx = false) /\ 

      (exists alloc', read_allocator p' self = Some alloc' /\
        exists idx', @frame_idx S n p' self frame = Ok idx' /\
          get_bit (@allocated S n alloc') idx' = true)   
  | Err => True  
  | Panic => False  
  end.
Proof.
Admitted.


End AllocateFrame.

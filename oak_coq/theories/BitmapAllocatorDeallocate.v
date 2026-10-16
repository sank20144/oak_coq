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
From OC Require Export BitmapAllocatorAllocate.

Local Open Scope string_scope.

Section DeallocateFrame.
Context {S : PageSize} {n : Uint63.int}.

(** Deallocation returns a frame to the available pool *)
Theorem deallocate_frame_correctness 
  (p : prog_state) (self : var_name) (frame : PhysFrame S) :

  (exists alloc, read_allocator p self = Some alloc /\ 
    @allocator_wf S n alloc) ->
  
  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                lifetime_active p lt = true /\
                ps_current_step p + 6 <= lt_end lt /\
                heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  (* The frame is within range and currently allocated *)
  (exists idx, @frame_idx S n p self frame = Ok idx /\
    exists alloc, read_allocator p self = Some alloc /\
      get_bit (@allocated S n alloc) idx = true) ->
  
  match @deallocate_frame S n p self frame with
  | Ok p' => 
      (* The frame was valid and allocated before *)
      (exists alloc, read_allocator p self = Some alloc /\
        exists idx, @frame_idx S n p self frame = Ok idx /\
          get_bit (valid alloc) idx = true /\           
          get_bit (@allocated S n alloc) idx = true) /\ 

      (* The frame becomes unallocated after *)
      (exists alloc', read_allocator p' self = Some alloc' /\
        exists idx', @frame_idx S n p' self frame = Ok idx' /\
          get_bit (@allocated S n alloc') idx' = false)   
  | Err => True  
  | Panic => False
  end.
Proof.
Admitted.


End DeallocateFrame.

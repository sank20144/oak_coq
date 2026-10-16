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
From OC Require Export BitmapAllocatorDeallocate.

Local Open Scope string_scope.


(** get_bit on the zero-initialised BitArray is always false *)
Lemma make_bitarray_get_bit_false {n : Uint63.int} (idx : Uint63.int) :
  get_bit (make_bitarray n) idx = false.
Proof.
Admitted.

(** No frame is currently allocated *)
Definition allocated_clear {S : PageSize} {n : Uint63.int}
    (alloc : BitmapAllocator S n) : Prop :=
  forall idx, get_bit (allocated alloc) idx = false.

Lemma allocated_clear_wf {S : PageSize} {n : Uint63.int}
    (alloc : BitmapAllocator S n) :
  allocated_clear alloc -> allocator_wf alloc.
Proof.
Admitted.

(** ** A freshly created allocator satisfies the ownership preconditions *)
Lemma new_allocator_satisfies_precond {S : PageSize} (n : Uint63.int)
    (p : prog_state) (var : var_name) (r : PhysFrameRange S) (lt_end_param : nat) :
  ps_current_step p + 6 < lt_end_param ->
  match new_allocator n p var r lt_end_param with
  | Some (p', _) =>
      exists a owner_lt m,
        var_lookup (ps_vars p') var = Some (VarMutOwned a owner_lt) /\
        lifetime_active p' owner_lt = true /\
        ps_current_step p' + 6 <= lt_end owner_lt /\
        heap_lookup (ps_heap p') a = Some (m, LocOwned)
  | None => True
  end.
Proof.
Admitted.

(** Setting an in-range bit that was already valid preserves allocator_wf **)
Lemma allocator_wf_set_allocated_true {S : PageSize} {n : Uint63.int}
  (alloc : BitmapAllocator S n) (idx : Uint63.int) :
  Uint63.to_nat idx < to_nat n * u64_bits ->
  get_bit (valid alloc) idx = true ->
  allocator_wf alloc ->
  allocator_wf (mkBitmapAllocator
                  (set_bit (allocated alloc) idx true)
                  (valid alloc)
                  (range alloc)).
Proof.
Admitted.

(** Setting any bit to false preserves allocator_wf **)
Lemma allocator_wf_set_allocated_false {S : PageSize} {n : Uint63.int}
  (alloc : BitmapAllocator S n) (idx : Uint63.int) :
  allocator_wf alloc ->
  allocator_wf (mkBitmapAllocator
                  (set_bit (allocated alloc) idx false)
                  (valid alloc)
                  (range alloc)).
Proof.
Admitted.

(* Initial allocator state*)

(** ** A freshly created allocator satisfies allocator_wf *)
Lemma new_allocator_wf {S : PageSize} (n : Uint63.int)
    (p : prog_state) (var : var_name) (r : PhysFrameRange S) (lt_end : nat) :
  match new_allocator n p var r lt_end with
  | Some (p', _) =>
      exists alloc, @read_allocator S n p' var = Some alloc /\
        @allocator_wf S n alloc
  | None => True
  end.
Proof.
Admitted.

(** ** fill with [true] preserves all bits that are already set *)
Lemma fill_true_preserves_set_bits {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  get_bit bits idx = true ->
  get_bit (@fill n bits start_idx end_idx true) idx = true.
Proof.
Admitted.

(** fill with false preserves bits that are already false **)
Lemma fill_false_preserves_false_bits {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  get_bit bits idx = false ->
  get_bit (@fill n bits start_idx end_idx false) idx = false.
Proof.
Admitted.

Lemma fold_left_set_false_neq {n : Uint63.int}
    (indices : list Uint63.int) (idx : Uint63.int) :
  (forall i, In i indices -> Uint63.eqb i idx = false) ->
  forall (init : BitArray n),
  get_bit (fold_left (fun acc j => set_bit acc j false) indices init) idx
  = get_bit init idx.
Proof.
Admitted.

(** ** mark_valid (with is_valid = true) preserves allocator_wf *)
Lemma mark_valid_true_preserves_wf {S : PageSize} {n : Uint63.int}
    (p : prog_state) (self : var_name) (frame_range : PhysFrameRange S) :

  (exists alloc, @read_allocator S n p self = Some alloc /\
    @allocator_wf S n alloc) ->

  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                  lifetime_active p lt = true /\
                  ps_current_step p + 6 <= lt_end lt /\
                  heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  match @mark_valid S n p self frame_range true with
  | Ok p' =>
      exists alloc', @read_allocator S n p' self = Some alloc' /\
        @allocator_wf S n alloc'
  | Err   => True
  | Panic => True 
  end.
Proof.
Admitted.

(** ** mark_valid preserves the ownership preconditions **)
Lemma mark_valid_preserves_precond {S : PageSize} {n : Uint63.int}
    (p : prog_state) (self : var_name) (frame_range : PhysFrameRange S)
    (is_valid : bool) :

  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                  lifetime_active p lt = true /\
                  ps_current_step p + 8 <= lt_end lt /\
                  heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  match @mark_valid S n p self frame_range is_valid with
  | Ok p' =>
      exists a lt m',
        var_lookup (ps_vars p') self = Some (VarMutOwned a lt) /\
        lifetime_active p' lt = true /\
        ps_current_step p' + 6 <= lt_end lt /\
        heap_lookup (ps_heap p') a = Some (m', LocOwned)
  | Err   => True
  | Panic => True
  end.
Proof.
Admitted.

(** ** fill false is identity outside its range, provided end_idx < wB **)  
Lemma fill_false_identity_outside {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  (end_idx < Z.to_nat Uint63.wB)%nat ->
  (Uint63.to_nat idx < start_idx \/ end_idx < Uint63.to_nat idx)%nat ->
  get_bit (@fill n bits start_idx end_idx false) idx = get_bit bits idx.
Proof.
Admitted.

Definition init_inv (S : PageSize) (n : Uint63.int)
    (p : prog_state) (self : var_name) (budget : nat) : Prop :=
  (exists alloc : BitmapAllocator S n,
      read_allocator p self = Some alloc /\ allocated_clear alloc) /\
  (exists a lt m,
      var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
      lifetime_active p lt = true /\
      ps_current_step p + budget <= lt_end lt /\
      heap_lookup (ps_heap p) a = Some (m, LocOwned)).

(** One mark_valid step preserves the invariant, for either validity bit. *)
Lemma mark_valid_step {S : PageSize} {n : Uint63.int}
    (p : prog_state) (self : var_name)
    (r : PhysFrameRange S) (b : bool) (k : nat) :
  init_inv S n p self (8 + k) ->
  match @mark_valid S n p self r b with
  | Ok p' => init_inv S n p' self (6 + k)
  | Err   => True
  | Panic => True
  end.
Proof.
Admitted.

Lemma allocator_wf_fill_valid_false {S : PageSize} {n : Uint63.int}
    (alloc : BitmapAllocator S n) (start_idx end_idx : nat) :
  (end_idx < Z.to_nat Uint63.wB)%nat ->
  (forall idx : Uint63.int,
      (start_idx <= Uint63.to_nat idx /\ Uint63.to_nat idx <= end_idx)%nat ->
      get_bit (allocated alloc) idx = false) ->
  allocator_wf alloc ->
  allocator_wf (mkBitmapAllocator
                  (allocated alloc)
                  (@fill n (valid alloc) start_idx end_idx false)
                  (range alloc)).
Proof.
Admitted.

(** The fold underlying init_allocator preserves the invariant on every
    successful prefix, given enough lifetime budget for the whole list. *)
Lemma init_fold_inv {S : PageSize} {n : Uint63.int} (self : var_name)
    (rs : list (PhysFrameRange S * bool)) :
  forall acc : Result prog_state,
    match acc with
    | Ok p  => init_inv S n p self (6 + 2 * length rs)
    | Err   => True
    | Panic => True
    end ->
    match fold_left
            (fun acc_p rv =>
               match acc_p with
               | Ok p' => @mark_valid S n p' self (fst rv) (snd rv)
               | Err => Err | Panic => Panic
               end) rs acc with
    | Ok p' => init_inv S n p' self 6
    | Err   => True
    | Panic => True
    end.
Proof.
Admitted.

Theorem deallocate_frame_preserves_wf {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (frame : PhysFrame S) :

  (exists alloc, read_allocator p self = Some alloc /\
    @allocator_wf S n alloc) ->

  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                lifetime_active p lt = true /\
                ps_current_step p + 6 <= lt_end lt /\
                heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  (exists idx, @frame_idx S n p self frame = Ok idx /\
    exists alloc, read_allocator p self = Some alloc /\
      get_bit (@allocated S n alloc) idx = true) ->

  match @deallocate_frame S n p self frame with
  | Ok p' =>
      exists alloc', read_allocator p' self = Some alloc' /\
        @allocator_wf S n alloc'
  | Err   => True
  | Panic => False
  end.
Proof.
Admitted.

(** ** mark_valid (with is_valid = false) preserves allocator_wf**) 
Lemma mark_valid_false_preserves_wf {S : PageSize} {n : Uint63.int}
    (p : prog_state) (self : var_name) (frame_range : PhysFrameRange S) :

  (exists alloc, @read_allocator S n p self = Some alloc /\
    @allocator_wf S n alloc) ->

  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                  lifetime_active p lt = true /\
                  ps_current_step p + 6 <= lt_end lt /\
                  heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  (forall p_ref ref_var alloc (start_idx end_idx : Uint63.int),
      @read_mut_allocator S n p self 6 = Some (p_ref, ref_var, alloc) ->
      @frame_idx S n p_ref ref_var (start_frame S frame_range) = Ok start_idx ->
      @frame_idx S n p_ref ref_var (end_frame S frame_range)   = Ok end_idx ->
      forall idx : Uint63.int,
        (Z.to_nat (Uint63.to_Z start_idx) <= Uint63.to_nat idx /\
         Uint63.to_nat idx <= Z.to_nat (Uint63.to_Z end_idx))%nat ->
        get_bit (allocated alloc) idx = false) ->

  match @mark_valid S n p self frame_range false with
  | Ok p' =>
      exists alloc', @read_allocator S n p' self = Some alloc' /\
        @allocator_wf S n alloc'
  | Err   => True
  | Panic => True
  end.
Proof.
Admitted.

(** Kernel initial-state correctness. Folding mark_valid over any list of
    (range, validity) pairs, with valid and invalid ranges
    interleaved yields a well-formed allocator, provided the lifetime covers
    the whole pass. *)
Theorem init_allocator_preserves_wf {S : PageSize} {n : Uint63.int}
    (p : prog_state) (self : var_name)
    (ranges : list (PhysFrameRange S * bool)) :
  init_inv S n p self (6 + 2 * length ranges) ->
  match @init_allocator S n p self ranges with
  | Ok p' => exists alloc' : BitmapAllocator S n,
      @read_allocator S n p' self = Some alloc' /\ @allocator_wf S n alloc'
  | Err   => True
  | Panic => True
  end.
Proof.
Admitted.

(** allocate_frame preserves the allocator well-formedness invariant **)
Theorem allocate_frame_preserves_wf {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) :

  (exists alloc, read_allocator p self = Some alloc /\
    @allocator_wf S n alloc) ->

  (exists a lt m, var_lookup (ps_vars p) self = Some (VarMutOwned a lt) /\
                lifetime_active p lt = true /\
                ps_current_step p + 6 <= lt_end lt /\
                heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->

  match @allocate_frame S n p self with
  | Ok (_, p') =>
      exists alloc', read_allocator p' self = Some alloc' /\
        @allocator_wf S n alloc'
  | Err   => True
  | Panic => False
  end.
Proof.
Admitted.

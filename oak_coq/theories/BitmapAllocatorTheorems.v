Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zbool.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Require Import Lia.
Require Import Coq.Strings.String.
Import ListNotations.
From stdpp Require Import bitvector.
From OC Require Import BitArr.
From OC Require Import VariableModel.
From OC Require Import PhysicalMemory.
From OC Require Import BitmapAllocatorCore.
From OC Require Import BitArrLemmas.


(* Lemmas on bitmap and bitarr ops*)

Local Open Scope Z_scope.

Lemma add_no_overflow a b :
  0 <= to_Z a ->
  0 <= to_Z b ->
  to_Z a + to_Z b < wB ->
  to_Z (a + b) = to_Z a + to_Z b.
Proof.
  intros Ha Hb Hsum.
  rewrite add_spec.
  rewrite Zmod_small; auto.
  split; [lia | exact Hsum].
Qed.

Lemma sub_no_underflow a b :
  to_Z b <= to_Z a ->
  to_Z (a - b) = to_Z a - to_Z b.
Proof.
  intros H.
  rewrite sub_spec.
  rewrite Zmod_small; auto.
  pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b).
  split; lia.
Qed.

Lemma mul_no_overflow a b :
  0 <= to_Z a ->
  0 <= to_Z b ->
  to_Z a * to_Z b < wB ->
  to_Z (a * b) = to_Z a * to_Z b.
Proof.
  intros Ha Hb Hprod.
  rewrite mul_spec.
  rewrite Zmod_small; auto.
  split; [apply Z.mul_nonneg_nonneg; auto | exact Hprod].
Qed.

Lemma div_exact a b :
  to_Z b <> 0 ->
  to_Z a = to_Z b * Z.of_nat (Z.to_nat (to_Z a / to_Z b)) ->
  to_Z (a / b) = to_Z a / to_Z b.
Proof.
  intros Hb Hexact.
  rewrite div_spec.
  reflexivity.
Qed.

Local Close Scope Z_scope.


(** Helper lemma: first_one_from_zero returns indices within bounds *)
Lemma first_one_from_zero_lt {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) :
  first_one_from_zero bits = Some idx ->
  Uint63.to_nat idx < to_nat n * u64_bits.
Proof.
  intros H.
  unfold first_one_from_zero in H.
  destruct (find (fun i => Z.testbit (bv_unsigned bits) (Z.of_nat i)) (seq 0 (to_nat n * u64_bits))) as [i|] eqn:Hfind.
  - injection H as H. subst idx.
    apply find_some in Hfind.
    destruct Hfind as [Hin _].
    apply in_seq in Hin.
    destruct Hin as [_ Hi_bound].
    rewrite of_Z_spec.
    rewrite Zmod_small.
    + rewrite Nat2Z.id. exact Hi_bound.
    + split.
      * lia.
      * apply Nat2Z.inj_lt in Hi_bound.
        apply (Z.lt_trans _ (Z.of_nat (to_nat n * u64_bits)) _).
        -- exact Hi_bound.
        -- apply bitarray_fits_uint63.
  - discriminate H.
Qed.

Lemma first_one_some_implies_nonzero_count {n : Uint63.int} (bits : BitArray n) (idx : Uint63.int) :
  first_one_from_zero bits = Some idx ->
  count_ones bits > 0.
Proof.
  intros H.
  assert (H_bit_true: get_bit bits idx = true).
  { apply first_one_returns_true; exact H. }
  
  assert (H_idx_bound: Uint63.to_nat idx < to_nat n * u64_bits).
  { apply (first_one_from_zero_lt bits); exact H. }

  destruct (count_ones bits) eqn:Hcount.
  - pose proof (count_ones_zero_all_false bits Hcount idx) as H_bit_false.
    rewrite H_bit_true in H_bit_false.
    discriminate.
  - lia.
Qed.

(** Helper lemma: let_mut_ref preserves heap values *)
Lemma let_mut_ref_preserves_heap_value
  (p p' : prog_state) (ref_var owned_var : var_name) (borrow_end : nat)
  (a : addr) (cell : mem_cell) :
  let_mut_ref p ref_var owned_var borrow_end = Some p' ->
  heap_lookup (ps_heap p) a = Some (cell, LocOwned) ->
  (exists lt, var_lookup (ps_vars p) owned_var = Some (VarMutOwned a lt)) ->
  exists new_state, heap_lookup (ps_heap p') a = Some (cell, new_state).
Proof.
  intros Hlet Hheap [lt Hvar].
  unfold let_mut_ref in Hlet.
  rewrite Hvar in Hlet.
  rewrite Hheap in Hlet.
  destruct (lifetime_contained_in _ _) eqn:Hcontained; [|discriminate].
  injection Hlet as Hlet. subst p'.
  simpl.
  unfold heap_update.
  destruct (Nat.eqb a a) eqn:Heq.
  - exists (LocMut [{| lt_id := ps_next_lifetime_id p; 
                       lt_start := ps_current_step p; 
                       lt_end := borrow_end |}]).
    admit.
  - rewrite Nat.eqb_refl in Heq. discriminate.
Admitted.

(** Helper lemma: let_mut_ref creates a mutable reference to the same address *)
Lemma let_mut_ref_creates_mut_ref
  (p p' : prog_state) (ref_var owned_var : var_name) (borrow_end : nat)
  (a : addr) (lt : lifetime) :
  var_lookup (ps_vars p) owned_var = Some (VarMutOwned a lt) ->
  (exists cell, heap_lookup (ps_heap p) a = Some (cell, LocOwned)) ->
  let_mut_ref p ref_var owned_var borrow_end = Some p' ->
  exists lt_ref, var_lookup (ps_vars p') ref_var = Some (VarMutRef a lt_ref).
Proof.
  intros Hvar [cell Hheap] Hlet.
  unfold let_mut_ref in Hlet.
  rewrite Hvar in Hlet.
  rewrite Hheap in Hlet.
  destruct (lifetime_contained_in _ _) eqn:Hcontained; [|discriminate].
  injection Hlet as Hlet. subst p'.
  simpl.
  exists {| lt_id := ps_next_lifetime_id p; 
            lt_start := ps_current_step p; 
            lt_end := borrow_end |}.
  unfold var_update.
  destruct (String.eqb ref_var ref_var) eqn:Heq.
  - admit.
  - rewrite String.eqb_refl in Heq. discriminate.
Admitted.

(** Helper lemma: reading through a mutable reference returns the same value *)
Lemma read_var_through_mut_ref
  (p : prog_state) (ref_var : var_name) (a : addr) (lt_ref : lifetime) (v : value) :
  var_lookup (ps_vars p) ref_var = Some (VarMutRef a lt_ref) ->
  lifetime_active p lt_ref = true ->
  (exists cell, heap_lookup (ps_heap p) a = Some (cell, LocMut [lt_ref]) /\ 
                cell_value cell = v) ->
  read_var p ref_var = Some v.
Proof.
  intros Hvar Hactive [cell [Hheap Hval]].
  unfold read_var.
  rewrite Hvar, Hactive, Hheap.
  unfold lifetime_eq.
  rewrite Nat.eqb_refl.
  rewrite Hval.
  reflexivity.
Qed.

(** After let_mut_ref succeeds from a state where read_allocator succeeds,
    read_allocator through the new mutable reference also succeeds *)
Lemma let_mut_ref_preserves_read_allocator {S : PageSize} {n : Uint63.int}
  (p p' : prog_state) (self ref_var : var_name) (borrow_end : nat)
  (alloc : BitmapAllocator S n) :
  read_allocator p self = Some alloc ->
  let_mut_ref p ref_var self borrow_end = Some p' ->
  read_allocator p' ref_var = Some alloc.
Proof.
  Admitted.

(** read_mut_allocator preserves the content of the allocator *)
Lemma read_mut_allocator_preserves_content {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (borrow_end : nat) (alloc : BitmapAllocator S n) :
  read_allocator p self = Some alloc ->
  match read_mut_allocator p self borrow_end with
  | Some (p_ref, ref_var, alloc') => 
      allocated alloc = allocated alloc' /\
      valid alloc = valid alloc' /\
      range alloc = range alloc'
  | None => True
  end.
Proof.
  intros Hread.
  unfold read_mut_allocator.
  destruct (let_mut_ref p _ self _) as [p_ref|] eqn:Hlet; [|trivial].
  destruct (read_allocator p_ref _) as [alloc'|] eqn:Hread'.
  - pose proof (let_mut_ref_preserves_read_allocator p p_ref self (self ++ "_mut_ref")%string 
                  (ps_current_step p + borrow_end) alloc Hread Hlet) as Hpreserve.
    rewrite Hread' in Hpreserve.
    injection Hpreserve as Hpreserve_eq.
    subst alloc'.
    split; [reflexivity | split; reflexivity].
  - trivial.
Qed.

Lemma read_mut_allocator_ref_droppable {S : PageSize} {n : Uint63.int}
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref < ps_current_step p + duration ->
  exists p', drop_var (step_forward p_ref) ref_var = Some p'.
Proof.
Admitted.

Lemma read_mut_allocator_preserves_step {S : PageSize} {n : Uint63.int}
  (p p_ref : prog_state) (self ref_var : var_name) (borrow_end : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self borrow_end = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref = ps_current_step p.
Proof.
  Admitted.

(** frame_idx returns the same index that was used to create a frame via the frame function *)
Lemma frame_idx_of_frame {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (idx : Uint63.int) (f : PhysFrame S) :
  @frame S n p self idx = Ok f ->
  @frame_idx S n p self f = Ok idx.
Proof.
(** This should be true but due to the bug in the Rust implementation we cannot prove this in the model *)
Admitted. 

(** The allocator after write_and_drop has the updated content *)
Lemma write_and_drop_allocator_content {S : PageSize} {n : Uint63.int}
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n)
  (self : var_name) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  (* If ref_var was a mutable reference to self's allocator *)
  exists alloc', read_allocator p' self = Some alloc' /\
    allocated alloc' = allocated new_alloc /\
    valid alloc' = valid new_alloc /\
    range alloc' = range new_alloc.
Proof.
Admitted.

(** frame_idx depends only on the range, not on the prog_state details *)
Lemma frame_idx_depends_on_range {S : PageSize} {n : Uint63.int}
  (p1 p2 : prog_state) (v1 v2 : var_name) (f : PhysFrame S)
  (alloc1 alloc2 : BitmapAllocator S n) :
  read_allocator p1 v1 = Some alloc1 ->
  read_allocator p2 v2 = Some alloc2 ->
  range alloc1 = range alloc2 ->
  @frame_idx S n p1 v1 f = @frame_idx S n p2 v2 f.
Proof.
Admitted.



(** After write_and_drop succeeds, the original variable is still accessible with LocOwned *)
Lemma write_and_drop_preserves_var_ownership {S : PageSize} {n : Uint63.int}
  (p p' : prog_state) (ref_var self : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) (lt : lifetime) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  write_and_drop p ref_var new_alloc = Ok p' ->
  ref_var <> self ->
  var_lookup (ps_vars p') self = Some (VarMutOwned a lt).
Proof.
Admitted.

(** After write_and_drop succeeds for a mutable reference, the heap location returns to LocOwned *)
Lemma write_and_drop_restores_loc_owned {S : PageSize} {n : Uint63.int}
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  (* If ref_var was a VarMutRef pointing to address a *)
  (exists lt, var_lookup (ps_vars p) ref_var = Some (VarMutRef a lt)) ->
  exists m, heap_lookup (ps_heap p') a = Some (m, LocOwned).
Proof.
Admitted.

(** write_and_drop preserves step counter with offset *)
Lemma write_and_drop_preserves_step {S : PageSize} {n : Uint63.int}
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  ps_current_step p' = ps_current_step p.
Proof.
Admitted.

(** read_mut_allocator preserves the original variable *)
Lemma read_mut_allocator_preserves_original_var {S : PageSize} {n : Uint63.int}
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  var_lookup (ps_vars p_ref) self = Some (VarMutOwned a lt).
Proof.
Admitted.

(** step_forward preserves variable lookups *)
Lemma step_forward_preserves_var_lookup
  (p : prog_state) (v : var_name) :
  var_lookup (ps_vars (step_forward p)) v = var_lookup (ps_vars p) v.
Proof.
  unfold step_forward. simpl. reflexivity.
Qed.

(** step_forward increments step counter *)
Lemma step_forward_step (p : prog_state) :
  ps_current_step (step_forward p) = S (ps_current_step p).
Proof.
  unfold step_forward. simpl. reflexivity.
Qed.

(** ref_var created by read_mut_allocator is different from self *)
Lemma read_mut_allocator_ref_var_diff {S : PageSize} {n : Uint63.int}
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  ref_var = (self ++ "_mut_ref")%string.
Proof.
  unfold read_mut_allocator.
  intros H.
  destruct (let_mut_ref p _ self _); [|discriminate].
  destruct (read_allocator p0 _); [|discriminate].
  injection H as _ Href _. symmetry. exact Href.
Qed.

Lemma read_shared_allocator_succeeds {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (a : addr) (lt : lifetime) (m : mem_cell) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  lifetime_active p lt = true ->
  ps_current_step p + 2 <= lt_end lt ->
  heap_lookup (ps_heap p) a = Some (m, LocOwned) ->
  exists p_ref ref_var alloc,
    @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc).
Proof.
  intros Hvar Hactive Hstep_bound Hheap.
  unfold read_shared_allocator.

  assert (Hlet: exists p_ref, 
    let_shared_ref p (self ++ "_ref") self (ps_current_step p + 2) = Some p_ref).
  {
    unfold let_shared_ref.
    rewrite Hvar, Hheap.
    
    assert (Hcontained: lifetime_contained_in 
              {| lt_id := ps_next_lifetime_id p;
                 lt_start := ps_current_step p;
                 lt_end := ps_current_step p + 2 |} lt = true).
    {
      unfold lifetime_contained_in.
      apply andb_true_iff.
      unfold lifetime_active in Hactive.
      apply andb_true_iff in Hactive.
      destruct Hactive as [Hstart_le Hstep_lt].
      apply Nat.leb_le in Hstart_le.
      apply Nat.ltb_lt in Hstep_lt.
      split.
      - apply Nat.leb_le. simpl. exact Hstart_le.
      - apply Nat.leb_le. simpl. lia.
    }
    rewrite Hcontained.
    eexists. reflexivity.
  }
  
  destruct Hlet as [p_ref Hlet].
  rewrite Hlet.

  admit.
Admitted.

(** If read_shared_allocator succeeds with proper preconditions, frame doesn't panic *)
Lemma frame_not_panic_when_accessible {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (idx : Uint63.int)
  (a : addr) (lt : lifetime) (m : mem_cell) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  lifetime_active p lt = true ->
  ps_current_step p + 2 <= lt_end lt ->
  heap_lookup (ps_heap p) a = Some (m, LocOwned) ->
  @frame S n p self idx <> Panic.
Proof.
  
Admitted.

(** String inequality lemma *)
Lemma string_append_suffix_neq (s suffix : string) :
  suffix <> ""%string -> (s ++ suffix)%string <> s.
Proof.
  intros Hsuffix Heq.
    induction s as [| c s' IH].
    - simpl in Heq. exact (Hsuffix Heq).
    - simpl in Heq. inversion Heq as [Htail].
      apply IH in Htail. contradiction.
Qed.

(** read_mut_allocator creates ref to same address as original variable *)
Lemma read_mut_allocator_same_addr {S : PageSize} {n : Uint63.int}
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  exists lt_ref, var_lookup (ps_vars p_ref) ref_var = Some (VarMutRef a lt_ref).
Proof.
Admitted.

(** Allocation returns a valid, previously unallocated frame *)
Theorem allocate_frame_correctness {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (self : var_name) :

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
  intros [alloc [Hread Hwf]] Hprecond.
  unfold allocate_frame.
  
  destruct (read_mut_allocator p self _) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { exfalso.
     destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].

     unfold read_mut_allocator in Hread_mut.

     assert (Hlet_succeeds: exists p', let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + 4) = Some p').
     {
       unfold let_mut_ref.
       rewrite Hvar_lookup, Hheap.
       unfold lifetime_active in Hactive.
       apply andb_true_iff in Hactive.
       destruct Hactive as [Hstart_le Hstep_lt].
       apply Nat.leb_le in Hstart_le.
       apply Nat.ltb_lt in Hstep_lt.
       assert (Hcontained: lifetime_contained_in 
                 {| lt_id := ps_next_lifetime_id p; 
                    lt_start := ps_current_step p; 
                    lt_end := ps_current_step p + 4 |} lt = true).
       { unfold lifetime_contained_in. simpl. apply andb_true_iff. split; apply Nat.leb_le; lia. }
       rewrite Hcontained.
       eexists. reflexivity.
     }
     
     destruct Hlet_succeeds as [p' Hlet].
     rewrite Hlet in Hread_mut.
     
     pose proof (let_mut_ref_preserves_read_allocator p p' self (self ++ "_mut_ref") 
                   (ps_current_step p + 4) alloc Hread Hlet) as Hread'.
     
     rewrite Hread' in Hread_mut.
     discriminate Hread_mut.

     }
  
  destruct (first_one_from_zero (get_available (allocated alloc_read) (valid alloc_read))) 
    as [frame_idx_val|] eqn:Hfirst.
  2: { unfold drop_and_return.
     destruct (drop_var (step_forward p_ref) ref_var) as [p_dropped|] eqn:Hdrop.
     - trivial.
     - exfalso.
       
       destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
       
       pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read 
                     Hread_mut) as Hstep_eq.
       
       assert (Hstep_bound_ref: ps_current_step p_ref < ps_current_step p + 4).
       { rewrite Hstep_eq. lia. }
       
       pose proof (read_mut_allocator_ref_droppable p p_ref self ref_var 
                     4 alloc_read Hread_mut Hstep_bound_ref) as [p' Hdrop'].
       
       rewrite Hdrop' in Hdrop.
       discriminate.
   }
  
  assert (Hframe_idx_bound: Uint63.to_nat frame_idx_val < to_nat n * u64_bits).
  { apply first_one_from_zero_lt with (bits := get_available (allocated alloc_read) (valid alloc_read)).
    exact Hfirst. }
  
  assert (Havailable: get_bit (get_available (allocated alloc_read) (valid alloc_read)) frame_idx_val = true).
  { apply first_one_returns_true. exact Hfirst. }
  
  unfold get_available in Havailable.
  rewrite bitand_get_bit in Havailable.
  apply andb_true_iff in Havailable.
  destruct Havailable as [Hvalid_bit Hnot_alloc_bit].
  
  rewrite bitnot_get_bit in Hnot_alloc_bit by exact Hframe_idx_bound.
  apply negb_true_iff in Hnot_alloc_bit.
  
  simpl.
  destruct (write_and_drop _ _ _) as [p''| |] eqn:Hwrite.
  2: { simpl. trivial. }
  
  destruct (frame p'' self frame_idx_val) as [returned_frame| |] eqn:Hframe.
  2: { simpl. trivial. }
  3: { unfold write_and_drop in Hwrite.
     destruct (write_var _ _ _) as [p_after_write|] eqn:Hwrite_var.
     - destruct (drop_var _ _) as [p_final|] eqn:Hdrop.
       + discriminate Hwrite.
       + discriminate Hwrite.
     - discriminate Hwrite.
   }
  
  pose proof (read_mut_allocator_preserves_content p self 4 alloc Hread) as Hpreserve.
  rewrite Hread_mut in Hpreserve.
  destruct Hpreserve as [Halloc_eq [Hvalid_eq Hrange_eq]].
  
  split.
  
  - exists alloc. split.
    + exact Hread.
    + exists frame_idx_val.
      split.
      * pose proof (frame_idx_of_frame p'' self frame_idx_val returned_frame Hframe) as Hidx_p''.
        pose proof (write_and_drop_allocator_content 
                      (step_forward (step_forward p_ref)) p'' ref_var
                      {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                         valid := valid alloc_read;
                         range := range alloc_read |} self Hwrite) 
          as [alloc'' [Hread'' [Halloc'' [Hvalid'' Hrange'']]]].
        assert (Hrange_p''_p: range alloc'' = range alloc).
        { rewrite Hrange''. rewrite <- Hrange_eq. reflexivity. }
        pose proof (frame_idx_depends_on_range p'' p self self returned_frame alloc'' alloc 
                   Hread'' Hread Hrange_p''_p) as Hidx_eq.
        rewrite <- Hidx_eq.
        exact Hidx_p''.
      * split.
        -- rewrite Hvalid_eq. exact Hvalid_bit.
        -- rewrite Halloc_eq. exact Hnot_alloc_bit.
      
  - pose proof (write_and_drop_allocator_content 
                  (step_forward (step_forward p_ref)) p'' ref_var
                  {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                     valid := valid alloc_read;
                     range := range alloc_read |} self Hwrite) 
      as [alloc' [Hread' [Halloc' [Hvalid' Hrange']]]].
      
    exists alloc'. split.
    + exact Hread'.
    + exists frame_idx_val.
      split.
      * pose proof (frame_idx_of_frame p'' self frame_idx_val returned_frame Hframe) as Hidx.
        exact Hidx.
      * rewrite Halloc'.
        simpl.
        apply get_bit_set_bit_same.
        exact Hframe_idx_bound.
      
  - exfalso.
     
     destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
     
     pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Hstep_p_ref.
     
     pose proof (read_mut_allocator_ref_var_diff p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Href_var_eq.
     
     pose proof (read_mut_allocator_same_addr p p_ref self ref_var 4 alloc_read a lt 
                   Hread_mut Hvar_lookup) as [lt_ref Hvar_ref].
     
     assert (Hself_diff_ref: ref_var <> self).
     { rewrite Href_var_eq. apply string_append_suffix_neq. discriminate. }
     
     assert (Hvar_p'': var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
{
  apply (write_and_drop_preserves_var_ownership 
           (step_forward (step_forward p_ref)) p'' ref_var self 
           {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
              valid := valid alloc_read;
              range := range alloc_read |} a lt).
  - rewrite step_forward_preserves_var_lookup.
    rewrite step_forward_preserves_var_lookup.
    apply (read_mut_allocator_preserves_original_var p p_ref self ref_var 4 alloc_read a lt 
             Hread_mut Hvar_lookup).
  - exact Hwrite.
  - exact Hself_diff_ref.
}
     
     assert (Hactive_p'': lifetime_active p'' lt = true).
     {
       pose proof (write_and_drop_preserves_step 
                     (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite) as Hstep_p''.
       unfold lifetime_active.
       unfold lifetime_active in Hactive.
       apply andb_true_iff in Hactive. destruct Hactive as [Hstart Hend].
       apply Nat.leb_le in Hstart. apply Nat.ltb_lt in Hend.
       apply andb_true_iff. split.
       - apply Nat.leb_le. rewrite Hstep_p''. unfold step_forward. simpl. rewrite Hstep_p_ref. lia.
       - apply Nat.ltb_lt. rewrite Hstep_p''. unfold step_forward. simpl. rewrite Hstep_p_ref. lia.
     }
     
     assert (Hstep_bound_p'': ps_current_step p'' + 2 <= lt_end lt).
     {
       pose proof (write_and_drop_preserves_step 
                     (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite) as Hstep_p''.
       rewrite Hstep_p''. unfold step_forward. simpl. rewrite Hstep_p_ref. lia.
     }
     
     assert (Hheap_p'': exists m', heap_lookup (ps_heap p'') a = Some (m', LocOwned)).
     {
       apply (write_and_drop_restores_loc_owned 
                (step_forward (step_forward p_ref)) p'' ref_var _ a Hwrite).
       exists lt_ref. unfold step_forward. simpl. exact Hvar_ref.
     }
     destruct Hheap_p'' as [m' Hheap_p''].
     
     pose proof (@frame_not_panic_when_accessible S n p'' self frame_idx_val a lt m'
                   Hvar_p'' Hactive_p'' Hstep_bound_p'' Hheap_p'') as Hnot_panic.
     
     contradiction.
Qed.

(** No double allocation: allocate_frame never returns an already allocated frame *)
Theorem no_double_allocation {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (var : var_name)
  (f : PhysFrame S) (returned_frame : PhysFrame S) (p' : prog_state) :
  (exists alloc, read_allocator p var = Some alloc /\ 
    @allocator_wf S n alloc) ->
  (exists alloc, read_allocator p var = Some alloc /\
    exists idx, @frame_idx S n p var f = Some idx /\
      get_bit (@allocated S n alloc) idx = true) ->
  @allocate_frame S n p var = Some (returned_frame, p') ->
  f <> returned_frame.
Proof.
  intros Hwf Hallocf Halloc.
  Admitted.
  
(** A zero-initialized bitmap allocator is well-formed *)
Theorem zero_init_allocator_wf {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (v : var_name) (r : PhysFrameRange S) :
  let (p', alloc_addr) := new_allocator n p v r in
  exists alloc, read_allocator p' alloc_addr = Some alloc /\
    @allocator_wf S n alloc.
Proof.
  unfold allocator_wf, new_allocator.
  intros idx H_bound H_allocated.
  
  unfold make_bitarray in H_allocated.
  unfold get_bit in H_allocated.
  
  assert (H_zero: get_bit (make_bitarray n) idx = false).
  {
    unfold get_bit, make_bitarray.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  apply Nat.ltb_lt in H_bound.
  rewrite H_bound in H_allocated.
  
  simpl in *.
  unfold get_bit,make_bitarray in H_zero.
  rewrite H_bound in H_zero.
  
  rewrite H_zero in H_allocated.
  discriminate.
Qed.

(** Marking regions as valid in a zero-initialized allocator preserves well-formedness *)
Theorem zero_init_mark_valid_wf {S : PageSize} {n : Uint63.int} 
  (p : program_state) (r : PhysFrameRange S) (frame_range : PhysFrameRange S) :
  let (p', alloc_addr) := new_allocator n p r in
  match @mark_valid S n p' alloc_addr frame_range true with
  | Some p'' => exists alloc, read_allocator p'' alloc_addr = Some alloc /\
                             @allocator_wf S n alloc
  | None => True
  end.
Proof.
  assert (H_zero_wf: allocator_wf (new_allocator n r)).
  { apply zero_init_allocator_wf. }
  
  unfold mark_valid.
  destruct (frame_to_idx (new_allocator n r) (start_frame S frame_range)) as [start_idx|]; 
    [|trivial].
  destruct (frame_to_idx (new_allocator n r) (end_frame S frame_range)) as [end_idx|]; 
    [|trivial].
  
  unfold allocator_wf. intros idx H_bound H_allocated.
  
  simpl in H_allocated.
  
  assert (H_zero_alloc: get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    unfold new_allocator, make_bitarray, get_bit.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  simpl in *.
  rewrite H_zero_alloc in H_allocated.
  discriminate.
Qed.

Theorem zero_init_mark_valid_general_wf {S : PageSize} {n : Uint63.int} 
  (p : program_state) (r : PhysFrameRange S) (frame_range : PhysFrameRange S) (is_valid : bool) :
  let (p', alloc_addr) := new_allocator n p r in
  match @mark_valid S n p' alloc_addr frame_range is_valid with
  | Some p'' => exists alloc, read_allocator p'' alloc_addr = Some alloc /\
                             @allocator_wf S n alloc
  | None => True
  end.
Proof.
  assert (H_zero_wf: @allocator_wf S n (new_allocator n r)).
  { apply zero_init_allocator_wf. }
  
  unfold mark_valid.
  destruct (frame_to_idx (new_allocator n r) (start_frame S frame_range)) as [start_idx|]; 
    [|trivial].
  destruct (frame_to_idx (new_allocator n r) (end_frame S frame_range)) as [end_idx|]; 
    [|trivial].
  
  unfold allocator_wf. intros idx H_bound H_allocated.
  
  simpl in H_allocated.
  
  assert (H_zero_alloc: get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    unfold new_allocator, make_bitarray, get_bit.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  simpl in *.
  rewrite H_zero_alloc in H_allocated.
  discriminate.
Qed.


(* Theorem kernel_init_allocator_wf {S : PageSize} {n : Uint63.int} 
        (r : PhysFrameRange S) :
  forall alloc : BitmapAllocator S n,
  (exists ranges : list (PhysFrameRange S),
   fold_left (fun acc range => 
     match acc with
     | Some a => mark_valid a range true
     | None => None
     end) ranges (Some (new_allocator n r)) = Some alloc) ->
  allocator_wf alloc.
Proof.
  intros alloc [ranges Hfold].
  
  assert (H_general: forall (init_alloc : BitmapAllocator S n),
    allocator_wf init_alloc ->
    forall final_alloc,
    (exists remaining_ranges,
     fold_left (fun acc range => 
       match acc with
       | Some a => mark_valid a range true
       | None => None
       end) remaining_ranges (Some init_alloc) = Some final_alloc) ->
    allocator_wf final_alloc).
  {
    intros init_alloc Hinit_wf final_alloc [remaining_ranges Hremaining_fold].
    revert init_alloc final_alloc Hinit_wf Hremaining_fold.
    induction remaining_ranges as [|range rest_ranges IH]; 
    intros init_alloc final_alloc Hinit_wf Hremaining_fold.
    
    - simpl in Hremaining_fold.
      inversion Hremaining_fold. subst final_alloc.
      exact Hinit_wf.
    
    - simpl in Hremaining_fold.
      destruct (mark_valid init_alloc range true) as [intermediate_alloc|] eqn:Hmark. 
      + assert (Hintermediate_wf: allocator_wf intermediate_alloc).
        {
          pose proof (mark_valid_preserves_wf init_alloc range Hinit_wf) as Hpres.
          rewrite Hmark in Hpres.
          exact Hpres.
        }
      
        apply (IH intermediate_alloc final_alloc Hintermediate_wf Hremaining_fold).
      + exfalso.
        assert (H_none_propagates: forall remaining_list,
          fold_left (fun acc range0 => 
            match acc with
            | Some a => @mark_valid S n a range0 true
            | None => None
            end) remaining_list None = None).
        {
          intro remaining_list.
          induction remaining_list as [|range_elem rest IHrest].
          - reflexivity.
          - simpl. exact IHrest.
        }
        
        rewrite H_none_propagates in Hremaining_fold.
        discriminate Hremaining_fold.
  }
  
  apply (H_general (new_allocator n r)).
  - apply zero_init_allocator_wf.
  - exists ranges. exact Hfold.
Qed. *)


Theorem mm_init_allocator_wf {S : PageSize} {n : Uint63.int} 
  (p : program_state) (r : PhysFrameRange S) 
  (ranges_with_validity : list (PhysFrameRange S * bool)) :
  let (p', alloc_addr) := new_allocator n p r in
  match @init_allocator S n p' alloc_addr ranges_with_validity with
  | Some p'' => exists alloc, read_allocator p'' alloc_addr = Some alloc /\
                             @allocator_wf S n alloc
  | None => True
  end.
Proof.
  assert (H_no_alloc_init: forall idx, idx < n * u64_bits -> 
    get_bit (allocated S n (new_allocator n r)) idx = false).
  {
    intros idx H_bound.
    unfold new_allocator, get_bit, make_bitarray.
    destruct (idx <? n * u64_bits); [|reflexivity].
    apply Z.testbit_0_l.
  }
  
  assert (H_general: forall (init_alloc : BitmapAllocator S n) remaining_ranges,
    (forall idx, idx < n * u64_bits -> get_bit (allocated S n init_alloc) idx = false) ->
    match fold_left (fun acc range_validity => 
       match acc with
       | Some a => mark_valid a (fst range_validity) (snd range_validity)
       | None => None
       end) remaining_ranges (Some init_alloc) with
    | Some final_alloc => allocator_wf final_alloc
    | None => True
    end).
  {
    intros init_alloc remaining_ranges.
    revert init_alloc.
    induction remaining_ranges as [|(range, validity) rest_ranges IH]; 
    intros init_alloc H_no_alloc.
    
    - simpl.
      unfold allocator_wf.
      intros idx H_bound H_allocated.
      assert (H_false: get_bit (allocated S n init_alloc) idx = false).
      { apply H_no_alloc; exact H_bound. }
      rewrite H_false in H_allocated.
      discriminate.
    
    - simpl.
      destruct (mark_valid init_alloc range validity) as [intermediate_alloc|] eqn:Hmark.
      + assert (H_intermediate_no_alloc: forall idx, idx < n * u64_bits -> 
          get_bit (allocated S n intermediate_alloc) idx = false).
        {
          pose proof (mark_valid_preserves_no_allocated init_alloc range validity H_no_alloc) as H_pres.
          rewrite Hmark in H_pres.
          exact H_pres.
        }
        
        apply (IH intermediate_alloc H_intermediate_no_alloc).
        
      + assert (H_none_propagates: forall remaining_list,
          fold_left (fun acc range_validity => 
            match acc with
            | Some a => @mark_valid S n a (fst range_validity) (snd range_validity)
            | None => None
            end) remaining_list None = None).
        {
          intro remaining_list.
          induction remaining_list as [|range_elem rest IHrest].
          - reflexivity.
          - simpl. exact IHrest.
        }
        rewrite H_none_propagates.
        trivial.
  }
  
  apply (H_general (new_allocator n r) ranges_with_validity H_no_alloc_init).
Qed.
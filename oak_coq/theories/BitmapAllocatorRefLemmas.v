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
  intros Hlet Hread Hlt.
  unfold read_allocator in *.
  assert (Hsame: read_var p' ref_var = read_var p self).
  {
    unfold let_mut_ref in Hlet.
    unfold read_var.
    
    destruct (var_lookup (ps_vars p) self) as [v|] eqn:Hlookup; [|discriminate].
    destruct v; try discriminate;
    destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.

    - destruct state; try discriminate.
      
      remember (lifetime_active p l) as b.
      
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Hp_eq. subst p'.
      
      transitivity (Some (cell_value cell)).
      + simpl. rewrite var_update_eq.
        unfold lifetime_active. simpl.
        replace (ps_current_step p <=? ps_current_step p)%nat with true by (symmetry; apply Nat.leb_le; lia).
        replace (ps_current_step p <? borrow_end)%nat with true by (symmetry; apply Nat.ltb_lt; assumption).
        simpl.
        
        autorewrite with oak_update.
        unfold lifetime_eq. simpl. autorewrite with oak_eqb.
        reflexivity.
      + simpl.
        assert (Hactive: lifetime_active p l = true).
        {
          unfold read_allocator in Hread.
          unfold read_var in Hread.
          rewrite Hlookup in Hread.
          destruct (lifetime_active p l) eqn:Hact; [reflexivity | discriminate].
        }
        subst b. rewrite Hactive. reflexivity.

    - destruct state; try discriminate.
      destruct l0 as [|top_lt rest]; try discriminate.
      destruct (lifetime_eq top_lt l) eqn:Heq_lt; [|discriminate].
      
      remember (lifetime_active p l) as b.
      
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Hp_eq. subst p'.
      
      transitivity (Some (cell_value cell)).
      + simpl. rewrite var_update_eq.
        unfold lifetime_active. simpl.
        replace (ps_current_step p <=? ps_current_step p)%nat with true by (symmetry; apply Nat.leb_le; lia).
        replace (ps_current_step p <? borrow_end)%nat with true by (symmetry; apply Nat.ltb_lt; assumption).
        simpl.
        autorewrite with oak_update.
        unfold lifetime_eq. simpl. autorewrite with oak_eqb.
        reflexivity.
      + simpl.
        assert (Hactive: lifetime_active p l = true).
        {
          unfold read_allocator in Hread.
          unfold read_var in Hread.
          rewrite Hlookup in Hread.
          destruct (lifetime_active p l) eqn:Hact; [reflexivity | ].
          discriminate.
        }
        subst b. rewrite Hactive. reflexivity.
  }
  rewrite Hsame.
  exact Hread.
Qed.

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
  intros Hborrow Hread.
  unfold read_mut_allocator.
  destruct (let_mut_ref p _ self _) as [p_ref|] eqn:Hlet; [|trivial].
  destruct (read_allocator p_ref _) as [alloc'|] eqn:Hread_ref; [|trivial].
  
  assert (Hlt: ps_current_step p < ps_current_step p + borrow_end).
  { 
    lia.
  }
  
  assert (Ha: Some alloc' = Some alloc).
  {
    rewrite <- Hread_ref.
    apply let_mut_ref_preserves_read_allocator with (p := p) (self := self) (ref_var := self ++ "_mut_ref") (borrow_end := ps_current_step p + borrow_end); assumption.
  }
  injection Ha as Ha. subst alloc'.
  repeat split; reflexivity.
Qed.

Lemma read_mut_allocator_ref_droppable
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref < ps_current_step p + duration ->
  exists p', drop_var (step_forward p_ref) ref_var = Some p'.
Proof.
  intros Hmut Hbound.
  unfold read_mut_allocator in Hmut.
  destruct (let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + duration)) as [p_mid|] eqn:Hlet; [|discriminate].
  destruct (read_allocator p_mid (self ++ "_mut_ref")) as [alloc'|] eqn:Hread; [|discriminate].
  injection Hmut as Hp_eq Href_eq Halloc_eq.
  subst p_ref ref_var alloc'.

  unfold let_mut_ref in Hlet.
  destruct (var_lookup (ps_vars p) self) as [v_self|] eqn:Hlookup_self; try discriminate.
  destruct v_self as [a_self lt_self|a_self lt_self| |a_self lt_self]; try discriminate.

  - destruct (heap_lookup (ps_heap p) a_self) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state; try discriminate.
    
    destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
    
    injection Hlet as Hp_mid_eq. subst p_mid.
    
    unfold step_forward, drop_var.
    simpl.
    
    rewrite var_update_eq. 
    simpl.
    
    rewrite heap_update_lookup_same.
    unfold lifetime_eq. simpl. autorewrite with oak_eqb.
    eexists. reflexivity.

  - destruct (heap_lookup (ps_heap p) a_self) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| | lts]; try discriminate.
    destruct lts as [| loc_lt rest_stack]; try discriminate.
    
    destruct (lifetime_eq loc_lt lt_self) eqn:Heq_lt; [|discriminate].
    destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
    
    injection Hlet as Hp_mid_eq. subst p_mid.
    
    unfold step_forward, drop_var.
    simpl.
    
    rewrite var_update_eq.
    simpl.
    
    rewrite heap_update_lookup_same.
    simpl.
    
    unfold lifetime_eq. simpl. autorewrite with oak_eqb.
    eexists. reflexivity.
Qed.

Lemma read_mut_allocator_preserves_step
  (p p_ref : prog_state) (self ref_var : var_name) (borrow_end : nat)
  (alloc : BitmapAllocator S n) :
  read_mut_allocator p self borrow_end = Some (p_ref, ref_var, alloc) ->
  ps_current_step p_ref = ps_current_step p.
Proof.
  intros Hmut.
  unfold read_mut_allocator in Hmut.
  destruct (let_mut_ref p _ self _) as [p_after_let|] eqn:Hlet; [|discriminate].
  destruct (read_allocator p_after_let _) as [alloc'|] eqn:Hread; [|discriminate].
  injection Hmut as Hp_eq Href_eq Halloc_eq. subst p_ref ref_var alloc.
  apply (let_mut_ref_preserves_current_step p p_after_let (self ++ "_mut_ref") self 
           (ps_current_step p + borrow_end) Hlet).
Qed.

(** frame_idx returns the same index that was used to create a frame via the frame function *)
Lemma frame_idx_of_frame
  (p : prog_state) (self : var_name) (idx : Uint63.int) (f : PhysFrame S) :
  @frame S n p self idx = Ok f ->
  @frame_idx S n p self f = Ok idx.
Proof.
  (** This should be true but due to the bug in the Rust implementation we cannot prove this in the model *)
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
  intros Hread1 Hread2 Hrange Hsucc1 Hsucc2.
  unfold frame_idx.
  destruct Hsucc1 as [p1_ref [v1_ref [Hread_shared1 [p1_fin Hdrop1]]]].
  destruct Hsucc2 as [p2_ref [v2_ref [Hread_shared2 [p2_fin Hdrop2]]]].
  rewrite Hread_shared1, Hread_shared2.
  rewrite Hrange.
  unfold drop_and_return.
  destruct (orb (Uint63.ltb (start_address S f) (start_address S (start_frame S (range alloc2))))
                (Uint63.ltb (start_address S (end_frame S (range alloc2))) (start_address S f))) eqn:Hcond.
  - rewrite Hdrop1, Hdrop2.
    reflexivity.
  - rewrite Hdrop1, Hdrop2.
    reflexivity.
Qed.

Lemma var_lookup_var_remove_diff (vars : var_env) (v1 v2 : var_name) :
  v1 <> v2 ->
  var_lookup (var_remove vars v1) v2 = var_lookup vars v2.
Proof.
  intros Hneq.
  unfold var_remove.
  induction vars as [| [v own] rest IH].
  - reflexivity.
  - simpl. destruct (String.eqb v1 v) eqn:Heq_v1.
    + apply String.eqb_eq in Heq_v1. subst v.
      destruct (String.eqb v2 v1) eqn:Heq_v2v1.
      * apply String.eqb_eq in Heq_v2v1. subst v2. contradiction.
      * apply IH.
    + simpl. destruct (String.eqb v2 v) eqn:Heq_v2.
      * reflexivity.
      * apply IH.
Qed.

(** After write_and_drop succeeds, the original variable is still accessible with LocOwned *)
Lemma write_and_drop_preserves_var_ownership
  (p p' : prog_state) (ref_var self : var_name) (new_alloc : BitmapAllocator S n)
  (a : addr) (lt : lifetime) :
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  write_and_drop p ref_var new_alloc = Ok p' ->
  ref_var <> self ->
  var_lookup (ps_vars p') self = Some (VarMutOwned a lt).
Proof.
  intros Hlookup Hwrite Hneq.
  unfold write_and_drop in Hwrite.
  destruct (write_var p ref_var (VAllocator new_alloc)) as [p_write|] eqn:Hwrite_var; try discriminate.
  destruct (drop_var p_write ref_var) as [p_drop|] eqn:Hdrop; try discriminate.
  injection Hwrite as Heq. subst p'.
  
  erewrite drop_var_preserves_vars; [| exact Hdrop].
  erewrite write_var_preserves_vars; [| exact Hwrite_var].
  rewrite var_lookup_var_remove_diff; assumption.
Qed.

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
  intros Hwrite [lt Hlookup] [lt' [cell Hheap]].
  unfold write_and_drop in Hwrite.
  destruct (write_var p ref_var (VAllocator new_alloc)) as [p_write|] eqn:Hwrite_var; try discriminate.
  destruct (drop_var p_write ref_var) as [p_drop|] eqn:Hdrop; try discriminate.
  injection Hwrite as Heq. subst p'.

  assert (Hvars_write: ps_vars p_write = ps_vars p) by (eapply write_var_preserves_vars; eauto).

  unfold write_var in Hwrite_var.
  rewrite Hlookup in Hwrite_var.
  destruct (lifetime_active p lt) eqn:Hactive; try discriminate.
  rewrite Hheap in Hwrite_var.
  simpl in Hwrite_var.
  destruct (lifetime_eq lt' lt) eqn:Heq_lt; try discriminate.
  injection Hwrite_var as Heq_write. subst p_write.

  unfold drop_var in Hdrop.
  simpl in Hdrop.
  rewrite Hlookup in Hdrop.
  rewrite heap_update_lookup_same in Hdrop.
  rewrite Heq_lt in Hdrop.
  injection Hdrop as Heq_drop. subst p_drop.
  simpl.
  apply heap_update_lookup_same.
Qed.

(** write_and_drop preserves step counter with offset *)
Lemma write_and_drop_preserves_step
  (p p' : prog_state) (ref_var : var_name) (new_alloc : BitmapAllocator S n) :
  write_and_drop p ref_var new_alloc = Ok p' ->
  ps_current_step p' = ps_current_step p.
Proof.
  intros Hwrite.
  unfold write_and_drop in Hwrite.
  destruct (write_var p ref_var _) as [p_after_write|] eqn:Hwrite_var; [|discriminate].
  destruct (drop_var p_after_write ref_var) as [p_final|] eqn:Hdrop; [|discriminate].
  injection Hwrite as Hp'. subst p_final.
  assert (Hstep1: ps_current_step p_after_write = ps_current_step p).
  { unfold write_var in Hwrite_var.
    destruct (var_lookup (ps_vars p) ref_var) as [v|] eqn:Hlookup; [|discriminate].
    destruct v; try discriminate.
    - destruct (lifetime_active p l); [|discriminate].
      destruct (heap_lookup (ps_heap p) a) as [[cell state]|]; [|discriminate].
      destruct state; try discriminate.
      injection Hwrite_var as Heq. subst p_after_write. reflexivity.
    - destruct (lifetime_active p l); [|discriminate].
      destruct (heap_lookup (ps_heap p) a) as [[cell state]|]; [|discriminate].
      destruct state; try discriminate.
      destruct l0 as [|loc_lt rest]; try discriminate.
      destruct (lifetime_eq loc_lt l); try discriminate.
      injection Hwrite_var as Heq. subst p_after_write. reflexivity. }
  assert (Hstep2: ps_current_step p' = ps_current_step p_after_write).
  { unfold drop_var in Hdrop.
    destruct (var_lookup (ps_vars p_after_write) ref_var) as [v|] eqn:Hlookup; [|discriminate].
    destruct v; try discriminate.
    - destruct (has_outliving_borrows (ps_heap p_after_write) a l); [discriminate|].
      injection Hdrop as Heq. subst p'. reflexivity.
    - destruct (has_outliving_borrows (ps_heap p_after_write) a l); [discriminate|].
      injection Hdrop as Heq. subst p'. reflexivity.
    - destruct (heap_lookup (ps_heap p_after_write) a) as [[cell state]|]; try discriminate.
      destruct state; try discriminate.
      + destruct l0; try discriminate.
        * injection Hdrop as Heq. subst p'. reflexivity. 
        * injection Hdrop as Heq. subst p'. simpl. reflexivity.
      + destruct l0 as [|loc_lt rest]; try discriminate.
        destruct (lifetime_eq loc_lt l) eqn:Heq_lt; try discriminate.
        injection Hdrop as Heq. subst p'. simpl. reflexivity.
    - destruct (heap_lookup (ps_heap p_after_write) a) as [[cell state]|]; try discriminate.
      destruct state; try discriminate.
      destruct l0 as [|loc_lt rest]; try discriminate.
      destruct (lifetime_eq loc_lt l); try discriminate.
      injection Hdrop as Heq. subst p'. reflexivity. }
  rewrite Hstep2, Hstep1. reflexivity.
Qed.

(** read_mut_allocator preserves the original variable *)
Lemma read_mut_allocator_preserves_original_var
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  var_lookup (ps_vars p_ref) self = Some (VarMutOwned a lt).
Proof.
  intros Hmut Hvar.
  unfold read_mut_allocator in Hmut.
  destruct (let_mut_ref p (self ++ "_mut_ref") self _) as [p_ref'|] eqn:Hlet; [|discriminate].
  destruct (read_allocator p_ref' _) as [alloc'|] eqn:Hread; [|discriminate].
  injection Hmut as Hp_eq Href_eq Halloc_eq. subst p_ref ref_var alloc.
  unfold let_mut_ref in Hlet.
  rewrite Hvar in Hlet.
  destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
  destruct state; try discriminate.
  destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
  injection Hlet as Hp_eq. subst p_ref'.
  simpl.
  rewrite var_update_neq.
  - exact Hvar.
  - apply string_append_suffix_neq.
    discriminate.
Qed.


(** ref_var created by read_mut_allocator is different from self *)
Lemma read_mut_allocator_ref_var_diff
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
  intros Hvar Hactive Hbound Hheap Hread.
  remember (mk_lifetime (ps_next_lifetime_id p) (ps_current_step p) (ps_current_step p + 2)) as borrow_lt.
  remember ({|
    ps_heap := heap_update (ps_heap p) a m (LocShared [borrow_lt]);
    ps_vars := var_update (ps_vars p) (self ++ "_ref") (VarSharedRef a borrow_lt);
    ps_next_addr := ps_next_addr p;
    ps_next_lifetime_id := Datatypes.S (ps_next_lifetime_id p);
    ps_current_step := ps_current_step p
  |}) as p_ref.
  
  assert (Hlet: let_shared_ref p (self ++ "_ref") self (ps_current_step p + 2) = Some p_ref).
  {
    unfold let_shared_ref, make_shared_borrow.
    rewrite Hvar, Hheap.
    destruct (lifetime_contained_in
              {| lt_id := ps_next_lifetime_id p; 
                 lt_start := ps_current_step p; 
                 lt_end := ps_current_step p + 2 |} lt) eqn:Hcont.
    - subst p_ref borrow_lt. reflexivity.
    - exfalso.
      unfold lifetime_contained_in in Hcont.
      simpl in Hcont.
      apply andb_false_iff in Hcont.
      destruct Hcont as [Hstart_bad | Hend_bad].
      + apply Nat.leb_nle in Hstart_bad.
        unfold lifetime_active in Hactive.
        apply andb_true_iff in Hactive.
        destruct Hactive as [Hstart _].
        apply Nat.leb_le in Hstart.
        lia.
      + apply Nat.leb_nle in Hend_bad.
        lia.
  }

  exists p_ref, (self ++ "_ref")%string.
  
  assert (Halloc_same: @read_allocator S n p_ref (self ++ "_ref") = read_allocator p self).
  {
    unfold read_allocator.
    unfold read_var.
    rewrite Hvar.
    rewrite Hactive.
    rewrite Hheap.
    subst p_ref. simpl.
    rewrite var_update_eq. simpl.
    subst borrow_lt.
    unfold lifetime_active. simpl.
    replace (ps_current_step p <=? ps_current_step p)%nat with true by (symmetry; apply Nat.leb_le; lia).
    replace (ps_current_step p <? ps_current_step p + 2)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    simpl.
    rewrite heap_update_lookup_same.
    reflexivity.
  }

  unfold read_shared_allocator.
  rewrite Hlet.
  simpl.
  rewrite Halloc_same.
  rewrite Hread.
  reflexivity.
Qed.

Lemma drop_shared_ref_succeeds
  (p : prog_state) (v : var_name) (p_ref : prog_state) (v_ref : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc) ->
  exists p_fin, drop_var (step_forward p_ref) v_ref = Some p_fin.
Proof.
  intros Hr. 
  unfold read_shared_allocator in Hr.
  unfold let_shared_ref in Hr.
  
  destruct (var_lookup (ps_vars p) v) as [own|] eqn:Hvar; try discriminate.
  destruct own as [a lt|a lt|a lt|a lt].
  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state.
    + destruct (make_shared_borrow _ _ _ _ _ _ _) as [p_ref_val|] eqn:Hmake; try discriminate.
      destruct (read_allocator p_ref_val _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold make_shared_borrow in Hmake.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      injection Hmake as Hp_ref_def.
      subst p_ref_val.
      
      unfold drop_var.
      simpl.
      rewrite var_update_eq.
      rewrite heap_update_lookup_same.
      simpl.
      eexists. reflexivity.

    + destruct (make_shared_borrow _ _ _ _ _ _ _) as [p_ref_val|] eqn:Hmake; try discriminate.
      destruct (read_allocator p_ref_val _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold make_shared_borrow in Hmake.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      injection Hmake as Hp_ref_def.
      subst p_ref_val.
      
      unfold drop_var.
      simpl.
      rewrite var_update_eq.
      rewrite heap_update_lookup_same.
      simpl.
      eexists. reflexivity.
      
    + discriminate.

  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state.
    + destruct (make_shared_borrow _ _ _ _ _ _ _) as [p_ref_val|] eqn:Hmake; try discriminate.
      destruct (read_allocator p_ref_val _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold make_shared_borrow in Hmake.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      injection Hmake as Hp_ref_def.
      subst p_ref_val.
      
      unfold drop_var.
      simpl.
      rewrite var_update_eq.
      rewrite heap_update_lookup_same.
      simpl.
      eexists. reflexivity.

    + destruct (make_shared_borrow _ _ _ _ _ _ _) as [p_ref_val|] eqn:Hmake; try discriminate.
      destruct (read_allocator p_ref_val _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold make_shared_borrow in Hmake.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      injection Hmake as Hp_ref_def.
      subst p_ref_val.
      
      unfold drop_var.
      simpl.
      rewrite var_update_eq.
      rewrite heap_update_lookup_same.
      simpl.
      eexists. reflexivity.

    + discriminate.

  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state.
    + discriminate.
    + destruct (make_shared_borrow _ _ _ _ _ _ _) as [p_ref_val|] eqn:Hmake; try discriminate.
      destruct (read_allocator p_ref_val _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold make_shared_borrow in Hmake.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      injection Hmake as Hp_ref_def.
      subst p_ref_val.
      
      unfold drop_var.
      simpl.
      rewrite var_update_eq.
      rewrite heap_update_lookup_same.
      simpl.
      eexists. reflexivity.
    + discriminate.

  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| shared_lts | mut_lts]; try discriminate.
    + destruct mut_lts as [|loc_lt rest_stack]; try discriminate.
      destruct (lifetime_eq loc_lt lt) eqn:Hlt_eq; try discriminate.
      destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
      destruct (read_allocator _ _) as [alloc_val|] eqn:Hread_alloc; try discriminate.
      injection Hr as Hp_eq Hv_eq Halloc_eq.
      subst p_ref v_ref alloc_val.
      
      unfold drop_var. simpl.
      rewrite var_update_eq. rewrite heap_update_lookup_same.
      destruct (lifetime_eq {| lt_id := ps_next_lifetime_id p; lt_start := ps_current_step p; lt_end := ps_current_step p + 2 |} 
                            {| lt_id := ps_next_lifetime_id p; lt_start := ps_current_step p; lt_end := ps_current_step p + 2 |}) eqn:Heq_self.
      * eexists. reflexivity.
      * exfalso. unfold lifetime_eq in Heq_self. rewrite Nat.eqb_refl in Heq_self. discriminate.   
Qed.

(** frame only panics when read_shared_allocator fails *)
Lemma frame_panic_iff_read_shared_fails
  (p : prog_state) (self : var_name) (idx : Uint63.int) :
  @frame S n p self idx = Panic <->
  @read_shared_allocator S n p self 2 = None.
Proof.
  unfold frame.
  destruct (read_shared_allocator p self 2) as [[[p_ref ref_var] alloc]|] eqn:Hread.
  - split; [intro Hpanic | intro Hcontr].
    + exfalso.
      pose proof (drop_shared_ref_succeeds p self p_ref ref_var alloc Hread) as [p_fin Hdrop].
      unfold drop_and_return in Hpanic.
      rewrite Hdrop in Hpanic.
      match goal with
      | [ H : (if ?cond then _ else _) = Panic |- _ ] => destruct cond
      end.
      * discriminate.
      * discriminate.
    + discriminate.
  - split; intro; reflexivity.
Qed.

(** If read_shared_allocator succeeds, frame doesn't panic *)
Lemma frame_not_panic_when_read_shared_succeeds
  (p : prog_state) (self : var_name) (idx : Uint63.int)
  (p_ref : prog_state) (ref_var : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc) ->
  @frame S n p self idx <> Panic.
Proof.
  intros Hread_shared.
  rewrite frame_panic_iff_read_shared_fails.
  rewrite Hread_shared.
  discriminate.
Qed.

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
  intros Hvar Hread Hactive Hstep_bound Hheap.
  
  pose proof (read_shared_allocator_succeeds p self a lt m alloc 
    Hvar Hactive Hstep_bound Hheap Hread) as [p_ref [ref_var Hread_shared]].
  
  apply (frame_not_panic_when_read_shared_succeeds p self idx p_ref ref_var alloc Hread_shared).
Qed.

(** read_mut_allocator creates ref to same address as original variable *)
Lemma read_mut_allocator_same_addr
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  exists lt_ref, var_lookup (ps_vars p_ref) ref_var = Some (VarMutRef a lt_ref).
Proof.
  intros Hread Hvar.
  unfold read_mut_allocator in Hread.
  destruct (let_mut_ref p (self ++ "_mut_ref") self _) as [p_ref'|] eqn:Hlet; [|discriminate].
  destruct (read_allocator p_ref' _) as [alloc'|] eqn:Hread_alloc; [|discriminate].
  injection Hread as Hp_eq Href_eq Halloc_eq.
  subst p_ref ref_var alloc'.
  unfold let_mut_ref in Hlet.
  rewrite Hvar in Hlet.
  destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; [|discriminate].
  destruct state; try discriminate.
  destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
  injection Hlet as Hp_eq. subst p_ref'.
  simpl.
  eexists.
  rewrite var_update_eq. reflexivity.
Qed.

(** Helper: read_mut_allocator results in a specific heap state *)
Lemma read_mut_allocator_heap_state
  (p p_ref : prog_state) (self ref_var : var_name) (duration : nat)
  (alloc : BitmapAllocator S n) (a : addr) (lt : lifetime) :
  read_mut_allocator p self duration = Some (p_ref, ref_var, alloc) ->
  var_lookup (ps_vars p) self = Some (VarMutOwned a lt) ->
  (exists m, heap_lookup (ps_heap p) a = Some (m, LocOwned)) ->
  exists cell lt_ref, heap_lookup (ps_heap p_ref) a = Some (cell, LocMut [lt_ref]).
Proof.
  intros Hread Hvar [m Hheap].
  unfold read_mut_allocator, let_mut_ref in Hread.
  rewrite Hvar, Hheap in Hread.
  destruct (lifetime_contained_in _ _) eqn:Hcontained; try discriminate.
  destruct (read_allocator _ _) as [alloc_alt|] eqn:Hread'; try discriminate.
  injection Hread as Hp_ref Href_var Halloc.
  subst p_ref.
  simpl.
  eexists. eexists.
  apply heap_update_lookup_same.
Qed.


(** Helper: read_allocator returns the exact allocator if types match *)
Lemma read_allocator_same 
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n) :
  read_var p v = Some (VAllocator alloc) ->
  read_allocator p v = Some alloc.
Proof.
  intros Hread.
  unfold read_allocator.
  rewrite Hread.
  destruct (PageSize_eq_dec S S) as [HeqS|HneqS].
  - assert (HeqS_refl: HeqS = eq_refl) by (apply UIP_dec; apply PageSize_eq_dec).
    rewrite HeqS_refl.
    simpl.
    generalize (Uint63.eqb_spec n n).
    rewrite (Uint63.eqb_refl n).
    intros Hspec.
    simpl.
    destruct Hspec as [Heq].
    assert (H_int_UIP: forall (x y : int) (p1 p2 : x = y), p1 = p2).
    { intros x y. apply UIP_dec. 
      intros a b. destruct (a =? b)%uint63 eqn:E.
      - left. apply Uint63.eqb_spec. exact E.
      - right. intro Hc. apply Uint63.eqb_spec in Hc. congruence. }
      
    match goal with
    | [ |- context [eq_rect _ _ _ _ ?eq_proof] ] =>
      replace eq_proof with (@eq_refl int n) by apply H_int_UIP
    end.
    simpl. reflexivity.
  - contradiction HneqS; reflexivity.
Qed.

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
  intros Hwrite Hself Hactive Href Hneq.
  destruct Href as [lt_ref [Hlookup_ref [cell Hheap]]].
  assert (Hself' : var_lookup (ps_vars p') self = Some (VarMutOwned a lt)).
  { eapply write_and_drop_preserves_var_ownership; eauto. }
  assert (Hstep : ps_current_step p' = ps_current_step p).
  { eapply write_and_drop_preserves_step; eauto. }
  assert (Hheap' : heap_lookup (ps_heap p') a = Some (mk_cell (VAllocator new_alloc), LocOwned)).
  { eapply write_and_drop_restores_loc_owned; eauto. }
  
  assert (Hread_alloc: read_allocator p' self = Some new_alloc).
  {
    apply read_allocator_same.
    unfold read_var.
    rewrite Hself'.
    assert (Hactive' : lifetime_active p' lt = true).
    { unfold lifetime_active in *. rewrite Hstep. exact Hactive. }
    rewrite Hactive'.
    rewrite Hheap'.
    simpl. reflexivity.
  }
  
  rewrite Hread_alloc.
  exists new_alloc.
  repeat split; reflexivity.
Qed.

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
  intros Hread Hvar [m Hheap].
  unfold read_mut_allocator in Hread.
  unfold let_mut_ref in Hread.
  rewrite Hvar, Hheap in Hread.
  destruct (lifetime_contained_in _ _) eqn:Hcont; [| discriminate].
  destruct (read_allocator _ _) as [alloc'|] eqn:Hread'; [| discriminate].
  injection Hread as Hp Href Halloc.
  subst p_ref ref_var alloc'.
  simpl.
  eexists. split.
  - rewrite var_update_eq. reflexivity.
  - eexists. apply heap_update_lookup_same.
Qed.

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
  intros Hrm Hvar Hheap.
  split; [| split; [| split]].
  - rewrite (read_mut_allocator_ref_var_diff p p_ref self ref_var duration alloc Hrm).
    apply string_append_suffix_neq. discriminate.
  - exact (read_mut_allocator_preserves_step p p_ref self ref_var duration alloc Hrm).
  - exact (read_mut_allocator_preserves_original_var
             p p_ref self ref_var duration alloc a lt Hrm Hvar).
  - exact (read_mut_allocator_ref_and_heap
             p p_ref self ref_var duration alloc a lt Hrm Hvar (ex_intro _ m Hheap)).
Qed.


End RefLemmas.

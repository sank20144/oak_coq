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

(** Allocation returns a valid, previously unallocated frame *)
Theorem allocate_frame_correctness 
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
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  unfold allocate_frame.
  
  destruct (read_mut_allocator p self _) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { exfalso.
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
     assert (Hlt_bound: ps_current_step p < ps_current_step p + 4).
     { lia. }
     pose proof (let_mut_ref_preserves_read_allocator p p' self (self ++ "_mut_ref") 
                   (ps_current_step p + 4) alloc Hlet Hread Hlt_bound) as Hread'.
     rewrite Hread' in Hread_mut.
     discriminate Hread_mut.
  }
  
  destruct (first_one_from_zero (get_available (allocated alloc_read) (valid alloc_read))) 
    as [frame_idx_val|] eqn:Hfirst.
  2: { unfold drop_and_return.
     destruct (drop_var (step_forward p_ref) ref_var) as [p_dropped|] eqn:Hdrop.
     - trivial.
     - exfalso.
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

  pose proof (read_mut_allocator_setup p p_ref self ref_var 4 alloc_read a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].
  assert (Hvar_input : var_lookup (ps_vars (step_forward (step_forward p_ref))) self = Some (VarMutOwned a lt)).
  { autorewrite with oak_step. exact Hvar_pref. }
  assert (Hactive_input : lifetime_active (step_forward (step_forward p_ref)) lt = true).
  { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }
  assert (Href_input : (exists lt_ref, var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var = Some (VarMutRef a lt_ref) /\
                              exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a = Some (cell, LocMut [lt_ref]))).
  { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
    exists lt_ref. split.
    - autorewrite with oak_step. exact Hvar_ref.
    - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }
  
  assert (H4pos : 4 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 4 alloc H4pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq' [Hvalid_eq' Hrange_eq']].
  assert (Heq_alloc: alloc = alloc_read).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  assert (Halloc_eq : allocated alloc = allocated alloc_read).
  { exact Halloc_eq'. }
  assert (Hvalid_eq : valid alloc = valid alloc_read).
  { exact Hvalid_eq'. }
  assert (Hrange_eq : range alloc = range alloc_read).
  { exact Hrange_eq'. }

  split.
  - exists alloc. split.
    + exact Hread.
    + exists frame_idx_val.
      split.
      * pose proof (frame_idx_of_frame p'' self frame_idx_val returned_frame Hframe) as Hidx_p''.
        pose proof (write_and_drop_allocator_content 
                      (step_forward (step_forward p_ref)) p'' ref_var self
                      {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                         valid := valid alloc_read;
                         range := range alloc_read |} a lt Hwrite Hvar_input Hactive_input Href_input Hneq) 
          as [alloc'' [Hread'' [Halloc'' [Hvalid'' Hrange'']]]].
        assert (Hrange_p''_p: range alloc'' = range alloc).
        { rewrite Hrange''. rewrite <- Hrange_eq. reflexivity. }
        
        assert (Hsucc1: (exists p1_ref v1_ref, @read_shared_allocator S n p'' self 2 = Some (p1_ref, v1_ref, alloc'') /\
                                     exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin)).
        {
          assert (Hstep_p'' : ps_current_step p'' = 2 + ps_current_step p).
          {
            rewrite (write_and_drop_preserves_step (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite).
            simpl. rewrite (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read Hread_mut).
            reflexivity.
          }
          assert (Hvar_p' : var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
          {
            apply (write_and_drop_preserves_var_ownership (step_forward (step_forward p_ref)) p'' ref_var self _ a lt Hvar_input Hwrite Hneq).
          }
          assert (Hactive_p'' : lifetime_active p'' lt = true).
          {
            unfold lifetime_active. rewrite Hstep_p''.
            finish_lifetime_active Hactive.
          }
          assert (Hstep_bound_p'' : (ps_current_step p'' + 2 <= lt_end lt)%nat).
          { rewrite Hstep_p''. lia. }
          assert (Hheap_p'' : exists m'', heap_lookup (ps_heap p'') a = Some (m'', LocOwned)).
          {
            eexists. apply (write_and_drop_restores_loc_owned (step_forward (step_forward p_ref)) p'' ref_var _ a Hwrite).
            -  pose proof (read_mut_allocator_same_addr p p_ref self ref_var 4 alloc_read a lt Hread_mut Hvar_lookup) as [lt_ref Hlookup_ref].
               exists lt_ref. rewrite !step_forward_preserves_var_lookup. exact Hlookup_ref.
            -  pose proof (read_mut_allocator_heap_state p p_ref self ref_var 4 alloc_read a lt Hread_mut Hvar_lookup) as Hheap_state.
               destruct Hheap_state as [cell [lt_ref_state Hheap_state]].
               { exists m. exact Hheap. }
               exists lt_ref_state, cell. rewrite !step_forward_preserves_heap_lookup. exact Hheap_state.
          }
          destruct Hheap_p'' as [m'' Hheap_p''].
          pose proof (read_shared_allocator_succeeds p'' self a lt m'' alloc'' Hvar_p' Hactive_p'' Hstep_bound_p'' Hheap_p'' Hread'') as [p1_ref [v1_ref Hread_shared1]].
          exists p1_ref, v1_ref. split; [exact Hread_shared1 |].
          apply (drop_shared_ref_succeeds p'' self p1_ref v1_ref alloc'' Hread_shared1).
        }
        
        assert (Hsucc2: (exists p2_ref v2_ref, @read_shared_allocator S n p self 2 = Some (p2_ref, v2_ref, alloc) /\
                                     exists p2_fin, drop_var (step_forward p2_ref) v2_ref = Some p2_fin)).
        {
          pose proof (read_shared_allocator_succeeds p self a lt m alloc Hvar_lookup Hactive (ltac:(lia)) Hheap Hread) as [p2_ref [v2_ref Hread_shared2]].
          exists p2_ref, v2_ref. split; [exact Hread_shared2 |].
          apply (drop_shared_ref_succeeds p self p2_ref v2_ref alloc Hread_shared2).
        }
        destruct Heq_alloc.
        pose proof (frame_idx_depends_on_range p'' p self self returned_frame alloc'' alloc 
                   Hread'' Hread Hrange_p''_p Hsucc1 Hsucc2) as Hidx_eq.
        rewrite <- Hidx_eq.
        exact Hidx_p''.
      * destruct Heq_alloc.
        split.
        -- exact Hvalid_bit.
        -- exact Hnot_alloc_bit.
        
  - pose proof (write_and_drop_allocator_content 
                   (step_forward (step_forward p_ref)) p'' ref_var self
                   {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                      valid := valid alloc_read;
                      range := range alloc_read |} a lt Hwrite Hvar_input Hactive_input Href_input Hneq) 
       as [alloc' [Hread' [Halloc' [Hvalid' Hrange']]]].
    exists alloc'. split.
    + exact Hread'.
    + exists frame_idx_val.
      split.
      * pose proof (frame_idx_of_frame p'' self frame_idx_val returned_frame Hframe) as H_idx_of.
        exact H_idx_of.
      * rewrite Halloc'. simpl.
        apply get_bit_set_bit_same.
        exact Hframe_idx_bound.
      
  - exfalso.
     pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Hstep_p_ref.
     pose proof (read_mut_allocator_ref_var_diff p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Href_var_eq.
     pose proof (read_mut_allocator_same_addr p p_ref self ref_var 4 alloc_read a lt 
                   Hread_mut Hvar_lookup) as [lt_ref Hvar_ref].
     assert (Hself_diff_ref: ref_var <> self).
     { rewrite Href_var_eq. apply string_append_suffix_neq. discriminate. }
     
     assert (Hvar_input3 : var_lookup (ps_vars (step_forward (step_forward p_ref))) self = Some (VarMutOwned a lt)).
     { autorewrite with oak_step.
       apply (read_mut_allocator_preserves_original_var p p_ref self ref_var 4 alloc_read a lt Hread_mut Hvar_lookup). }
     assert (Hactive_input3 : lifetime_active (step_forward (step_forward p_ref)) lt = true).
     { unfold lifetime_active. simpl. rewrite Hstep_p_ref.
       finish_lifetime_active Hactive. }
     assert (Href_input3 : (exists lt_ref0, var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var = Some (VarMutRef a lt_ref0) /\
                                  exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a = Some (cell, LocMut [lt_ref0]))).
     { pose proof (read_mut_allocator_ref_and_heap p p_ref self ref_var 4 alloc_read a lt
                     Hread_mut Hvar_lookup (ex_intro _ m Hheap)) as [lt_ref0 [Hvar_ref0 Hheap_ref0]].
       exists lt_ref0. split.
       - autorewrite with oak_step. exact Hvar_ref0.
       - destruct Hheap_ref0 as [cell_ref0 Hheap_ref0].
         autorewrite with oak_step.
         exists cell_ref0. exact Hheap_ref0. }

     assert (Hvar_p'' : var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
     {
       apply (write_and_drop_preserves_var_ownership 
                (step_forward (step_forward p_ref)) p'' ref_var self 
                {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                   valid := valid alloc_read;
                   range := range alloc_read |} a lt).
       - exact Hvar_input3.
       - exact Hwrite.
       - exact Hself_diff_ref.
     }
     
     assert (Hactive_p'' : lifetime_active p'' lt = true).
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
     
     assert (Hstep_bound_p'' : ps_current_step p'' + 2 <= lt_end lt).
     {
       pose proof (write_and_drop_preserves_step 
                     (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite) as Hstep_p''.
       rewrite Hstep_p''. unfold step_forward. simpl. rewrite Hstep_p_ref. lia.
     }
     
     assert (Hheap_p'' : exists cell, heap_lookup (ps_heap p'') a = Some (cell, LocOwned)).
     {
       eexists.
       apply (write_and_drop_restores_loc_owned 
                (step_forward (step_forward p_ref)) p'' ref_var _ a Hwrite).
       - exists lt_ref. unfold step_forward. simpl. exact Hvar_ref.
       - rewrite !step_forward_preserves_heap_lookup.
         pose proof (read_mut_allocator_heap_state p p_ref self ref_var 4 alloc_read a lt 
                      Hread_mut Hvar_lookup) as Hheap_state.
         destruct Hheap_state as [cell [lt_ref_state Hheap_state]].
         { exists m. exact Hheap. }
         exists lt_ref_state, cell. exact Hheap_state.
     }
     destruct Hheap_p'' as [m' Hheap_p''].
     
     pose proof (write_and_drop_allocator_content (step_forward (step_forward p_ref)) p'' ref_var self 
         {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
            valid := valid alloc_read;
            range := range alloc_read |} a lt Hwrite Hvar_input3 Hactive_input3 Href_input3 Hself_diff_ref) as [alloc_p'' [Hread_p'' _]].
    
     pose proof (@frame_not_panic_when_accessible S n p'' self frame_idx_val alloc_p'' a lt m'
                   Hvar_p'' Hread_p'' Hactive_p'' Hstep_bound_p'' Hheap_p'') as Hnot_panic.
     
     contradiction.
Qed.

(** If read_allocator and read_shared_allocator both succeed on the same variable,
    they return the same allocator. *)
Lemma read_shared_allocator_returns_same_alloc
  (p : prog_state) (v : var_name) (alloc : BitmapAllocator S n)
  (p_ref : prog_state) (v_ref : var_name) (alloc' : BitmapAllocator S n) :
  read_allocator p v = Some alloc ->
  @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc') ->
  alloc' = alloc.
Proof.
  intros Hread Hshared.
  unfold read_shared_allocator in Hshared.
  destruct (let_shared_ref p _ v _) as [p_let|] eqn:Hlet; [|discriminate].
  destruct (@read_allocator S n p_let (v ++ "_ref")) as [alloc_let|] eqn:Hread_let; [|discriminate].
  injection Hshared as _ _ Halloc'. subst alloc'.
  unfold read_allocator in Hread, Hread_let.
  unfold read_var in Hread, Hread_let.
  unfold let_shared_ref in Hlet.
  destruct (var_lookup (ps_vars p) v) as [own|] eqn:Hvar; [|discriminate].
  destruct own as [a lt_v|a lt_v|a lt_v|a lt_v]; try discriminate.
  - destruct (lifetime_active p lt_v) eqn:Hactive; [|discriminate].
    destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| lts |]; try discriminate.
    + unfold make_shared_borrow in Hlet.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      simpl in Hread_let.
      
      destruct (can_read LocOwned) eqn:Hcan; simpl in *; try discriminate.
      congruence.
    + unfold make_shared_borrow in Hlet.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      simpl in Hread_let.
      
      destruct (can_read (LocShared lts)) eqn:Hcan; simpl in *; try discriminate.
      congruence.
  - destruct (lifetime_active p lt_v) eqn:Hactive; [|discriminate].
    destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| lts |]; try discriminate.
    + unfold make_shared_borrow in Hlet.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      simpl in Hread_let.
      
      destruct (can_read LocOwned) eqn:Hcan; simpl in *; try discriminate.
      congruence.
    + unfold make_shared_borrow in Hlet.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      simpl in Hread_let.
      
      destruct (can_read (LocShared lts)) eqn:Hcan; simpl in *; try discriminate.
      congruence.
  - destruct (lifetime_active p lt_v) eqn:Hactive; [|discriminate].
    destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| lts | mut_lts]; try discriminate.
    + unfold make_shared_borrow in Hlet.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      simpl in Hread_let.
      
      congruence.
  - destruct (lifetime_active p lt_v) eqn:Hactive; [|discriminate].
    destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state as [| shared_lts | mut_lts]; try discriminate.
    + destruct mut_lts as [|loc_lt rest_stack]; try discriminate.
      destruct (lifetime_eq loc_lt lt_v) eqn:Hlt_eq; try discriminate.
      destruct (lifetime_contained_in _ _) eqn:Hcont; [|discriminate].
      injection Hlet as Heq. subst p_let. simpl in Hread_let.
      rewrite var_update_eq in Hread_let. simpl in Hread_let.
      unfold lifetime_active in Hread_let.
      simpl in Hread_let.
      replace (ps_current_step p <=? ps_current_step p)%nat with true in Hread_let by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true in Hread_let by (symmetry; apply Nat.ltb_lt; lia).
      simpl in Hread_let.
      rewrite heap_update_lookup_same in Hread_let.
      unfold lifetime_eq in Hread_let. simpl in Hread_let.
      rewrite Nat.eqb_refl in Hread_let. simpl in Hread_let.
      rewrite Hread in Hread_let. simpl in Hread_let.
      destruct (PageSize_eq_dec S S) as [Seq|]; [|contradiction].
      assert (HeqS_refl: Seq = eq_refl) by (apply UIP_dec; apply PageSize_eq_dec).
      clear HeqS_refl Seq. simpl in Hread_let.
      congruence.
Qed.

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
  intros Hread [a [lt [m [Hvar [Hactive [Hstep Hheap]]]]]].
  pose proof (read_shared_allocator_succeeds p v a lt m alloc Hvar Hactive Hstep Hheap Hread) as [p_ref [v_ref Hrs]].
  exists p_ref, v_ref. split; [exact Hrs|].
  apply (drop_shared_ref_succeeds p v p_ref v_ref alloc Hrs).
Qed.

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
  intros Hread [a [lt [lt_ref [Hvar [Hactive [Hstep [cell [Hheap_lookup Hcont]]]]]]]].
  
  set (borrow_lt := mk_lifetime (ps_next_lifetime_id p) (ps_current_step p) (ps_current_step p + 2)).
  set (p_ref := {|
    ps_heap := heap_update (ps_heap p) a cell (LocMut (borrow_lt :: lt_ref :: nil));
    ps_vars := var_update (ps_vars p) (v ++ "_ref") (VarSharedRef a borrow_lt);
    ps_next_addr := ps_next_addr p;
    ps_next_lifetime_id := Datatypes.S (ps_next_lifetime_id p);
    ps_current_step := ps_current_step p
  |}).
  
  exists p_ref, (v ++ "_ref").
  split.
  - unfold read_shared_allocator.
    assert (Hlet: let_shared_ref p (v ++ "_ref") v (ps_current_step p + 2) = Some p_ref).
    {
      unfold let_shared_ref.
      rewrite Hvar.
      rewrite Hheap_lookup.
      unfold lifetime_eq.
      simpl.
      rewrite Nat.eqb_refl.
      rewrite Hcont.
      subst p_ref.
      subst borrow_lt.
      reflexivity.
    }
    rewrite Hlet.
    simpl.
    
    assert (Hread_ref: @read_allocator S n p_ref (v ++ "_ref") = Some alloc).
    {
      unfold read_allocator in *.
      unfold read_var in *.
      simpl.
      rewrite var_update_eq.
      simpl.
      rewrite heap_update_lookup_same.
      subst borrow_lt.
      unfold lifetime_active. simpl.
      replace (ps_current_step p <=? ps_current_step p)%nat with true by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? ps_current_step p + 2)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      simpl.
      unfold lifetime_eq. simpl. rewrite Nat.eqb_refl.
      
      rewrite Hvar in Hread.
      rewrite Hactive in Hread.
      rewrite Hheap_lookup in Hread.
      unfold lifetime_eq in Hread. rewrite Nat.eqb_refl in Hread.
      simpl in Hread.
      destruct (cell_value cell) as [| | | | | | | | S' n' alloc']; try discriminate.
      destruct (PageSize_eq_dec S S') as [e|]; try discriminate.
      subst S'.
      simpl in Hread. inversion Hread. clear Hread. subst.
      
      assert (H_int_UIP: forall (x y : int) (p1 p2 : x = y), p1 = p2).
      { intros x0 y0. apply UIP_dec. 
        intros i j. destruct (i =? j)%uint63 eqn:E.
        - left. apply Uint63.eqb_spec. exact E.
        - right. intro Hc. apply Uint63.eqb_spec in Hc. congruence. }
      
      simpl.
      
      reflexivity.
    }
    unfold read_shared_allocator.
    simpl.
    rewrite Hread_ref. reflexivity.

  - eexists.
    unfold drop_var.
    unfold step_forward; simpl.
    rewrite var_update_eq.
    rewrite heap_update_lookup_same.
    simpl.
    unfold lifetime_eq. simpl.
    rewrite Nat.eqb_refl.
    eexists.
Qed.

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
  intros Hread1 Hread2 Hrange Hsucc1 Hsucc2.
  apply (frame_idx_depends_on_range p1 p2 v1 v2 f alloc1 alloc2 Hread1 Hread2 Hrange Hsucc1 Hsucc2).
Qed.

(** frame_idx only panics when read_shared_allocator fails *)
Lemma frame_idx_panic_iff_read_shared_fails
  (p : prog_state) (self : var_name) (frame : PhysFrame S) :
  @frame_idx S n p self frame = Panic <->
  @read_shared_allocator S n p self 2 = None.
Proof.
  split.
  - intro Hpanic.
    unfold frame_idx in Hpanic.
    destruct (@read_shared_allocator S n p self 2) as [[[p_ref ref_var] alloc]|] eqn:Hread.
    + pose proof (drop_shared_ref_succeeds p self p_ref ref_var alloc Hread) as [p_fin Hdrop].
      unfold drop_and_return in Hpanic.
      destruct (_ || _)%bool;
        rewrite Hdrop in Hpanic; discriminate.
    + reflexivity.
  - intro Hnone.
    unfold frame_idx.
    rewrite Hnone.
    reflexivity.
Qed.

(** If read_shared_allocator succeeds, frame_idx doesn't panic *)
Lemma frame_idx_not_panic_when_read_shared_succeeds
  (p : prog_state) (self : var_name) (frame : PhysFrame S)
  (p_ref : prog_state) (ref_var : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p self 2 = Some (p_ref, ref_var, alloc) ->
  @frame_idx S n p self frame <> Panic.
Proof.
  intros Hread_shared.
  rewrite frame_idx_panic_iff_read_shared_fails.
  rewrite Hread_shared.
  discriminate.
Qed.


End AllocateFrame.

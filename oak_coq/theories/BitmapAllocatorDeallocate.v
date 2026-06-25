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
  intros [alloc [Hread Hwf]] Hprecond Hframe_precond.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  destruct Hframe_precond as [fidx_pre [Hfidx_pre [alloc_f [Hread_f Halloc_pre]]]].
  rewrite Hread in Hread_f. injection Hread_f as Hread_f. subst alloc_f.
  unfold deallocate_frame.
  
  destruct (read_mut_allocator p self _) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { exfalso.
     unfold read_mut_allocator in Hread_mut.
     assert (Hlet_succeeds: exists p', let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + 6) = Some p').
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
                    lt_end := ps_current_step p + 6 |} lt = true).
       { unfold lifetime_contained_in. simpl. apply andb_true_iff. split; apply Nat.leb_le; lia. }
       rewrite Hcontained.
       eexists. reflexivity.
     }
     destruct Hlet_succeeds as [p' Hlet].
     rewrite Hlet in Hread_mut.
     assert (Hlt_bound: ps_current_step p < ps_current_step p + 6).
     { lia. }
     pose proof (let_mut_ref_preserves_read_allocator p p' self (self ++ "_mut_ref") 
                   (ps_current_step p + 6) alloc Hlet Hread Hlt_bound) as Hread'.
     rewrite Hread' in Hread_mut.
     discriminate Hread_mut.
  }
  
  assert (H6pos : 6 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 6 alloc H6pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq' [Hvalid_eq' Hrange_eq']].
  assert (Heq_alloc: alloc_read = alloc).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.
  
  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].
  
  assert (Hread_pref: read_allocator p_ref ref_var = Some alloc).
  { unfold read_mut_allocator in Hread_mut.
    destruct (let_mut_ref _ _ _ _) as [p'|] eqn:Hlet; [|discriminate].
    destruct (read_allocator p' _) as [a'|] eqn:Hra; [|discriminate].
    injection Hread_mut as Hp Hr Ha. subst. exact Hra. }
  
  assert (Hpre_p: exists a0 lt0 m0, var_lookup (ps_vars p) self = Some (VarMutOwned a0 lt0) /\
                lifetime_active p lt0 = true /\
                ps_current_step p + 2 <= lt_end lt0 /\
                heap_lookup (ps_heap p) a0 = Some (m0, LocOwned)).
  { exists a, lt, m. repeat split; auto. lia. }
  
  destruct (@frame_idx S n p_ref ref_var frame) as [fidx| |] eqn:Hfidx.
  
  - assert (Hfidx_transfer: @frame_idx S n p self frame = Ok fidx).
    { assert (Hsucc_pref: exists p1_ref v1_ref, @read_shared_allocator S n p_ref ref_var 2 = Some (p1_ref, v1_ref, alloc) /\
                           exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin).
      {
        unfold read_mut_allocator in Hread_mut.
        destruct (let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + 6)) as [p_let|] eqn:Hlet_mut; [|discriminate].
        destruct (read_allocator p_let (self ++ "_mut_ref")) eqn:Hread_plet.
        2: { simpl in Hread_mut. discriminate. }
        injection Hread_mut as Hp_eq Href_eq Halloc_eq.
        subst p_let ref_var.
        rewrite Halloc_eq in Hread_plet.

        unfold let_mut_ref in Hlet_mut.
        rewrite Hvar_lookup in Hlet_mut.
        rewrite Hheap in Hlet_mut.
        destruct (lifetime_contained_in _ _) eqn:Hcont_mut; [|discriminate].
        injection Hlet_mut as Hp_ref_eq. rewrite <- Hp_ref_eq in *.

        set (lt_borrow := {| lt_id := ps_next_lifetime_id p; 
                             lt_start := ps_current_step p; 
                             lt_end := ps_current_step p + 6 |}).

        apply (read_shared_allocator_succeeds_from_mut_ref _ (self ++ "_mut_ref") alloc Hread_plet).
        
        exists a, lt, lt_borrow.
        repeat split.
        - simpl. rewrite var_update_eq. reflexivity.
        - unfold lifetime_active. simpl.
          apply andb_true_iff. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
        - simpl. lia.
        - eexists. split.
          + simpl. rewrite heap_update_lookup_same. reflexivity.
          + unfold lifetime_contained_in. simpl. apply andb_true_iff. split; apply Nat.leb_le; lia.
      }
      
      assert (Hsucc_p: exists p2_ref v2_ref, @read_shared_allocator S n p self 2 = Some (p2_ref, v2_ref, alloc) /\
                           exists p2_fin, drop_var (step_forward p2_ref) v2_ref = Some p2_fin).
      {
        apply (read_shared_allocator_succeeds_from_alloc p self alloc Hread).
        exists a, lt, m. repeat split; auto. lia.
      }
      
      pose proof (frame_idx_transfer p_ref p ref_var self frame alloc alloc
                    Hread_pref Hread (eq_refl (range alloc)) Hsucc_pref Hsucc_p) as Hidx_eq.
      rewrite <- Hidx_eq. exact Hfidx. }
    
    destruct (negb (get_bit (valid alloc) fidx)) eqn:Hvalid_check.
    
    + exfalso.
      apply negb_true_iff in Hvalid_check.
      rewrite Hfidx_transfer in Hfidx_pre. injection Hfidx_pre as Hfidx_eq. subst fidx_pre.
      assert (Hfidx_bound: Uint63.to_nat fidx < to_nat n * u64_bits).
      { destruct (Nat.ltb_spec (Uint63.to_nat fidx) (to_nat n * u64_bits)) as [Hlt|Hge].
        - exact Hlt.
        - exfalso. rewrite get_bit_bounds in Halloc_pre by exact Hge. discriminate. }
      pose proof (Hwf fidx Hfidx_bound Halloc_pre) as Hvalid_from_wf.
      rewrite Hvalid_check in Hvalid_from_wf. discriminate.
    
    + apply negb_false_iff in Hvalid_check.
      
      destruct (negb (get_bit (allocated alloc) fidx)) eqn:Halloc_check.
      
      * exfalso.
        apply negb_true_iff in Halloc_check.
        rewrite Hfidx_transfer in Hfidx_pre. injection Hfidx_pre as Hfidx_eq. subst fidx_pre.
        rewrite Halloc_pre in Halloc_check. discriminate.
      
      * apply negb_false_iff in Halloc_check.
        
        assert (Hvar_input : var_lookup (ps_vars (step_forward (step_forward (step_forward (step_forward p_ref))))) self = Some (VarMutOwned a lt)).
        { autorewrite with oak_step. exact Hvar_pref. }
        assert (Hactive_input : lifetime_active (step_forward (step_forward (step_forward (step_forward p_ref)))) lt = true).
        { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }
        assert (Href_input : (exists lt_ref, var_lookup (ps_vars (step_forward (step_forward (step_forward (step_forward p_ref))))) ref_var = Some (VarMutRef a lt_ref) /\
                                    exists cell, heap_lookup (ps_heap (step_forward (step_forward (step_forward (step_forward p_ref))))) a = Some (cell, LocMut [lt_ref]))).
        { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
          exists lt_ref. split.
          - autorewrite with oak_step. exact Hvar_ref.
          - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }
        
        destruct (write_and_drop _ _ _) as [p''| |] eqn:Hwrite.
        
        -- split.
           
           ++ exists alloc. split; [exact Hread|].
              exists fidx. split; [exact Hfidx_transfer|].
              split; [exact Hvalid_check|exact Halloc_check].
           
           ++ pose proof (write_and_drop_allocator_content 
                            (step_forward (step_forward (step_forward (step_forward p_ref)))) p'' ref_var self
                            {| allocated := set_bit (allocated alloc) fidx false;
                               valid := valid alloc;
                               range := range alloc |} a lt Hwrite Hvar_input Hactive_input Href_input Hneq) 
                 as [alloc' [Hread' [Halloc' [Hvalid' Hrange']]]].
              exists alloc'. split; [exact Hread'|].
              exists fidx. split.
              ** assert (Hrange_p'_p: range alloc' = range alloc).
                 { rewrite Hrange'. reflexivity. }
                 
                 assert (Hpre_p'': exists a2 lt2 m2, var_lookup (ps_vars p'') self = Some (VarMutOwned a2 lt2) /\
                               lifetime_active p'' lt2 = true /\
                               ps_current_step p'' + 2 <= lt_end lt2 /\
                               heap_lookup (ps_heap p'') a2 = Some (m2, LocOwned)).
                 {
                   assert (Hstep_p'' : ps_current_step p'' = 4 + ps_current_step p).
                   {
                     rewrite (write_and_drop_preserves_step (step_forward (step_forward (step_forward (step_forward p_ref)))) p'' ref_var _ Hwrite).
                     simpl. rewrite (read_mut_allocator_preserves_step p p_ref self ref_var 6 alloc Hread_mut).
                     reflexivity.
                   }
                   assert (Hvar_p'' : var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
                   {
                     apply (write_and_drop_preserves_var_ownership (step_forward (step_forward (step_forward (step_forward p_ref)))) p'' ref_var self _ a lt Hvar_input Hwrite Hneq).
                   }
                   assert (Hactive_p'' : lifetime_active p'' lt = true).
                   {
                     unfold lifetime_active. rewrite Hstep_p''.
                     finish_lifetime_active Hactive.
                   }
                   assert (Hheap_p'' : exists m'', heap_lookup (ps_heap p'') a = Some (m'', LocOwned)).
                   {
                     eexists. apply (write_and_drop_restores_loc_owned (step_forward (step_forward (step_forward (step_forward p_ref)))) p'' ref_var _ a Hwrite).
                     - pose proof (read_mut_allocator_same_addr p p_ref self ref_var 6 alloc a lt Hread_mut Hvar_lookup) as [lt_ref Hlookup_ref].
                       exists lt_ref. rewrite !step_forward_preserves_var_lookup. exact Hlookup_ref.
                     - pose proof (read_mut_allocator_heap_state p p_ref self ref_var 6 alloc a lt Hread_mut Hvar_lookup) as Hheap_state.
                       destruct Hheap_state as [cell [lt_ref_state Hheap_state]].
                       { exists m. exact Hheap. }
                       exists lt_ref_state, cell. rewrite !step_forward_preserves_heap_lookup. exact Hheap_state.
                   }
                   destruct Hheap_p'' as [m'' Hheap_p''].
                   exists a, lt, m''. repeat split; auto.
                   rewrite Hstep_p''. lia.
                 }
                 
                  assert (Hsucc_p'': exists p1_ref v1_ref, @read_shared_allocator S n p'' self 2 = Some (p1_ref, v1_ref, alloc') /\
                               exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin).
                  {
                    destruct Hpre_p'' as [a2 [lt2 [m2 [Hvar_p'' [Hactive_p'' [Hstep_p'' Hheap_p'']]]]]].
                    apply (read_shared_allocator_succeeds_from_alloc p'' self alloc' Hread').
                    exists a2, lt2, m2. repeat split; auto.
                  }
                  
                  assert (Hsucc_p: exists p2_ref v2_ref, @read_shared_allocator S n p self 2 = Some (p2_ref, v2_ref, alloc) /\
                               exists p2_fin, drop_var (step_forward p2_ref) v2_ref = Some p2_fin).
                  {
                    destruct Hpre_p as [a0 [lt0 [m0 [Hvar_p [Hactive_p [Hstep_p Hheap_p]]]]]].
                    apply (read_shared_allocator_succeeds_from_alloc p self alloc Hread).
                    exists a0, lt0, m0. repeat split; auto.
                  }

                  pose proof (frame_idx_transfer p'' p self self frame alloc' alloc
                               Hread' Hread Hrange_p'_p Hsucc_p'' Hsucc_p) as Hidx_eq.
                  rewrite Hidx_eq. exact Hfidx_transfer.
                 
                 
              ** rewrite Halloc'. simpl.
                 assert (Hfidx_bound: Uint63.to_nat fidx < to_nat n * u64_bits).
                 {
                   destruct (Nat.ltb_spec (Uint63.to_nat fidx) (to_nat n * u64_bits)) as [Hlt|Hge].
                   - exact Hlt.
                   - exfalso.
                     rewrite get_bit_bounds in Hvalid_check by exact Hge.
                     discriminate.
                 }
                 apply get_bit_set_bit_same.
                 exact Hfidx_bound.
        
        -- trivial.
        
        -- exfalso.
           unfold write_and_drop in Hwrite.
           destruct (write_var _ _ _) as [p_after_write|] eqn:Hwrite_var.
           ++ destruct (drop_var _ _) as [p_final|] eqn:Hdrop;
              discriminate Hwrite.
           ++ discriminate Hwrite.
  
  - exfalso.
    assert (Hsucc_pref: exists p1_ref v1_ref, @read_shared_allocator S n p_ref ref_var 2 = Some (p1_ref, v1_ref, alloc) /\
                           exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin).
    {
      unfold read_mut_allocator in Hread_mut.
      destruct (let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + 6)) as [p_let|] eqn:Hlet_mut; [|discriminate].
      destruct (read_allocator p_let (self ++ "_mut_ref")) eqn:Hread_plet; [|discriminate].
      injection Hread_mut as Hp_eq Href_eq Halloc_eq.
      subst p_let ref_var.
      rewrite Halloc_eq in Hread_plet.
      
      unfold let_mut_ref in Hlet_mut.
      rewrite Hvar_lookup in Hlet_mut.
      rewrite Hheap in Hlet_mut.
      destruct (lifetime_contained_in _ _) eqn:Hcont_mut; [|discriminate].
      injection Hlet_mut as Hp_ref_eq. rewrite <- Hp_ref_eq in *.
      
      set (lt_borrow := {| lt_id := ps_next_lifetime_id p; 
                           lt_start := ps_current_step p; 
                           lt_end := ps_current_step p + 6 |}).

      apply (read_shared_allocator_succeeds_from_mut_ref _ (self ++ "_mut_ref") alloc Hread_plet).
      
      exists a, lt, lt_borrow.
      repeat split.
      - simpl. rewrite var_update_eq. reflexivity.
      - unfold lifetime_active. simpl.
        apply andb_true_iff. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
      - simpl. lia.
      - eexists. split.
        + simpl. rewrite heap_update_lookup_same. reflexivity.
        + unfold lifetime_contained_in. simpl. apply andb_true_iff. split; apply Nat.leb_le; lia.
    }

    assert (Hsucc_p: exists p2_ref v2_ref, @read_shared_allocator S n p self 2 = Some (p2_ref, v2_ref, alloc) /\
                           exists p2_fin, drop_var (step_forward p2_ref) v2_ref = Some p2_fin).
    {
      apply (read_shared_allocator_succeeds_from_alloc p self alloc Hread).
      exists a, lt, m. repeat split; auto. lia.
    }

    pose proof (frame_idx_transfer p_ref p ref_var self frame alloc alloc
                  Hread_pref Hread (eq_refl (range alloc)) Hsucc_pref Hsucc_p) as Hidx_eq.
    rewrite <- Hidx_eq in Hfidx_pre.
    rewrite Hfidx in Hfidx_pre. discriminate.
  
  - exfalso.
    
    assert (Hsucc_pref : exists p1_ref v1_ref, @read_shared_allocator S n p_ref ref_var 2 = Some (p1_ref, v1_ref, alloc) /\
                           exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin).
    {
      unfold read_mut_allocator in Hread_mut.
      destruct (let_mut_ref p (self ++ "_mut_ref") self (ps_current_step p + 6)) as [p_let|] eqn:Hlet_mut; [|discriminate].
      destruct (read_allocator p_let (self ++ "_mut_ref")) eqn:Hread_plet; [|discriminate].
      injection Hread_mut as Hp_eq Href_eq Halloc_eq.
      subst p_let ref_var.
      rewrite Halloc_eq in Hread_plet.

      unfold let_mut_ref in Hlet_mut.
      rewrite Hvar_lookup in Hlet_mut.
      rewrite Hheap in Hlet_mut.
      destruct (lifetime_contained_in _ _) eqn:Hcont_mut; [|discriminate].
      injection Hlet_mut as Hp_ref_eq. rewrite <- Hp_ref_eq in *.

      set (lt_borrow := {| lt_id := ps_next_lifetime_id p; 
                           lt_start := ps_current_step p; 
                           lt_end := ps_current_step p + 6 |}).

      apply (read_shared_allocator_succeeds_from_mut_ref _ (self ++ "_mut_ref") alloc Hread_plet).
      
      exists a, lt, lt_borrow.
      repeat split.
      - simpl. rewrite var_update_eq. reflexivity.
      - unfold lifetime_active. simpl.
        apply andb_true_iff. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
      - simpl. lia.
      - eexists. split.
        + simpl. rewrite heap_update_lookup_same. reflexivity.
        + unfold lifetime_contained_in. simpl. apply andb_true_iff. split; apply Nat.leb_le; lia.
    }
    
    destruct Hsucc_pref as [p1_ref [v1_ref [Hread_shared _]]].
    apply (frame_idx_not_panic_when_read_shared_succeeds p_ref ref_var frame p1_ref v1_ref alloc Hread_shared).
    exact Hfidx.
Qed.


End DeallocateFrame.

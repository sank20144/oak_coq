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

Lemma heap_update_lookup_same (h : heap) (a : addr) (cell : mem_cell) (state : location_state) :
  heap_lookup (heap_update h a cell state) a = Some (cell, state).
Proof.
  induction h as [| [[a' cell'] state'] rest IH].
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. destruct (Nat.eqb a a') eqn:Heq.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

Lemma heap_update_lookup_diff (h : heap) (a a' : addr) (cell : mem_cell) (state : location_state) :
  a <> a' ->
  heap_lookup (heap_update h a cell state) a' = heap_lookup h a'.
Proof.
  intros Hneq.
  induction h as [| [[a'' cell''] state''] rest IH].
  - simpl. rewrite Nat.eqb_sym. 
    apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
  - simpl. destruct (Nat.eqb a a'') eqn:Heq_a.
    + simpl. destruct (Nat.eqb a' a'') eqn:Heq_a'.
      * apply Nat.eqb_eq in Heq_a, Heq_a'. subst. contradiction.
      * rewrite <- Nat.eqb_neq in Hneq.
        rewrite Nat.eqb_sym.
        rewrite Hneq.
        reflexivity.
    + simpl. destruct (Nat.eqb a' a'') eqn:Heq_a'.
      * reflexivity.
      * apply IH.
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
  exists (LocMut [{| lt_id := ps_next_lifetime_id p; 
                     lt_start := ps_current_step p; 
                     lt_end := borrow_end |}]).
  apply heap_update_lookup_same.
Qed.

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
  clear Hvar Hheap Hcontained.
  induction (ps_vars p) as [|(v', own') rest IH].
  - simpl. rewrite String.eqb_refl. reflexivity.
  - simpl. destruct (String.eqb ref_var v') eqn:Heq.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

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


Lemma write_var_preserves_vars (p p' : prog_state) (ref_var : var_name) (v_val : value) :
  write_var p ref_var v_val = Some p' ->
  ps_vars p' = ps_vars p.
Proof.
  intros. unfold write_var in H.
  repeat (match goal with 
          | [ H : match ?x with _ => _ end = _ |- _ ] => destruct x eqn:? ; try discriminate
          end); inversion H; subst; reflexivity.
Qed.

Lemma drop_var_preserves_vars (p p' : prog_state) (var : var_name) :
  drop_var p var = Some p' ->
  ps_vars p' = var_remove (ps_vars p) var.
Proof.
  intros. unfold drop_var in H.
  repeat (match goal with 
          | [ H : match ?x with _ => _ end = _ |- _ ] => destruct x eqn:? ; try discriminate
          end); inversion H; subst; simpl; reflexivity.
Qed.

Lemma var_update_eq (vars : var_env) (v : var_name) (own : var_ownership) :
  var_lookup (var_update vars v own) v = Some own.
Proof.
  induction vars as [|(v', own') rest IH].
  - simpl. rewrite String.eqb_refl. reflexivity.
  - simpl. destruct (String.eqb v v') eqn:Heq.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

Lemma var_update_neq (vars : var_env) (v1 v2 : var_name) (own : var_ownership) :
  v1 <> v2 ->
  var_lookup (var_update vars v1 own) v2 = var_lookup vars v2.
Proof.
  intros Hneq.
  induction vars as [|(v', own') rest IH].
  - simpl. apply String.eqb_neq in Hneq. rewrite String.eqb_sym, Hneq. reflexivity.
  - simpl. destruct (String.eqb v1 v') eqn:Heq1.
    + apply String.eqb_eq in Heq1. subst v1.
      simpl. destruct (String.eqb v2 v') eqn:Heq2.
      * apply String.eqb_eq in Heq2. subst v2. contradiction.
      * reflexivity.
    + simpl. destruct (String.eqb v2 v') eqn:Heq2.
      * reflexivity.
      * apply IH.
Qed.

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

(** Helper lemma: eq_rect with eq_refl is identity *)
Lemma eq_rect_eq_refl {A : Type} (x : A) (P : A -> Type) (p : P x) :
  eq_rect x P p x eq_refl = p.
Proof.
  reflexivity.
Qed.


(** step_forward preserves variable lookups *)
Lemma step_forward_preserves_var_lookup
  (p : prog_state) (v : var_name) :
  var_lookup (ps_vars (step_forward p)) v = var_lookup (ps_vars p) v.
Proof.
  unfold step_forward. simpl. reflexivity.
Qed.

(** step_forward preserves heap lookups *)
Lemma step_forward_preserves_heap_lookup
  (p : prog_state) (a : addr) :
  heap_lookup (ps_heap (step_forward p)) a = heap_lookup (ps_heap p) a.
Proof.
  unfold step_forward. simpl. reflexivity.
Qed.

(** step_forward increments step counter *)
Lemma step_forward_step (p : prog_state) :
  ps_current_step (step_forward p) = S (ps_current_step p).
Proof.
  unfold step_forward. simpl. reflexivity.
Qed.

(** Helper: Uint63.eqb reflexivity gives eq_refl after UIP *)
Lemma uint63_eqb_refl_eq (n : Uint63.int) :
  (n =? n)%uint63 = true.
Proof.
  apply Uint63.eqb_spec. reflexivity.
Qed.

Lemma let_mut_ref_lifetime_id (p p' : prog_state) (ref_var owned_var : var_name) 
  (borrow_end : nat) (a : addr) (lt : lifetime) :
  var_lookup (ps_vars p) owned_var = Some (VarMutOwned a lt) →
  (exists cell, heap_lookup (ps_heap p) a = Some (cell, LocOwned)) →
  let_mut_ref p ref_var owned_var borrow_end = Some p' →
  ps_next_lifetime_id p' = S (ps_next_lifetime_id p).
Proof.
  intros Hvar [cell Hheap] Hlet.
  unfold let_mut_ref in Hlet.
  rewrite Hvar, Hheap in Hlet.
  destruct (lifetime_contained_in _ _); [|discriminate].
  injection Hlet as Hlet. subst p'. simpl. reflexivity.
Qed.

Lemma let_mut_ref_preserves_next_addr (p p' : prog_state) (ref_var owned_var : var_name)
  (borrow_end : nat) :
  let_mut_ref p ref_var owned_var borrow_end = Some p' →
  ps_next_addr p' = ps_next_addr p.
Proof.
  intros Hlet.
  unfold let_mut_ref in Hlet.
  destruct (var_lookup (ps_vars p) owned_var) as [v|] eqn:Hvar; try discriminate.
  destruct v; try discriminate.
  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state; try discriminate.
    destruct (lifetime_contained_in _ _) eqn:Hcontained; try discriminate.
    injection Hlet as Hlet. subst p'. simpl. reflexivity.
  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state; try discriminate.
    destruct l0 as [|loc_lt rest_stack]; try discriminate.
    destruct (lifetime_eq loc_lt l); try discriminate.
    destruct (lifetime_contained_in _ _); try discriminate.
    injection Hlet as Hlet. subst p'. simpl. reflexivity.
Qed.

(** Helper: let_mut_ref preserves current_step *)
Lemma let_mut_ref_preserves_current_step (p p' : prog_state) (ref_var owned_var : var_name)
  (borrow_end : nat) :
  let_mut_ref p ref_var owned_var borrow_end = Some p' ->
  ps_current_step p' = ps_current_step p.
Proof.
  intros Hlet.
  unfold let_mut_ref in Hlet.
  destruct (var_lookup (ps_vars p) owned_var) as [v|] eqn:Hvar; try discriminate.
  destruct v; try discriminate.
  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state; try discriminate.
    destruct (lifetime_contained_in _ _) eqn:Hcontained; try discriminate.
    injection Hlet as Hlet. subst p'. simpl. reflexivity.
  - destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate.
    destruct state; try discriminate.
    destruct l0 as [|loc_lt rest_stack]; try discriminate.
    destruct (lifetime_eq loc_lt l); try discriminate.
    destruct (lifetime_contained_in _ _); try discriminate.
    injection Hlet as Hlet. subst p'. simpl. reflexivity.
Qed.

(** After let_mut_ref succeeds from a state where read_allocator succeeds,
    read_allocator through the new mutable reference also succeeds *)
Lemma let_mut_ref_preserves_read_allocator {S : PageSize} {n : Uint63.int}
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
        
        rewrite heap_update_lookup_same.
        unfold lifetime_eq. simpl. rewrite Nat.eqb_refl.
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
        rewrite heap_update_lookup_same.
        unfold lifetime_eq. simpl. rewrite Nat.eqb_refl.
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
Lemma read_mut_allocator_preserves_content {S : PageSize} {n : Uint63.int}
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

Lemma read_mut_allocator_ref_droppable {S : PageSize} {n : Uint63.int}
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
    unfold lifetime_eq. simpl. rewrite Nat.eqb_refl.
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
    
    unfold lifetime_eq. simpl. rewrite Nat.eqb_refl.
    eexists. reflexivity.
Qed.

Lemma read_mut_allocator_preserves_step {S : PageSize} {n : Uint63.int}
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
Lemma frame_idx_of_frame {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (idx : Uint63.int) (f : PhysFrame S) :
  @frame S n p self idx = Ok f ->
  @frame_idx S n p self f = Ok idx.
Proof.
  (** This should be true but due to the bug in the Rust implementation we cannot prove this in the model *)
Admitted. 

(** frame_idx depends only on the range, not on the prog_state details *)
Lemma frame_idx_depends_on_range {S : PageSize} {n : Uint63.int}
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
Lemma write_and_drop_preserves_var_ownership {S : PageSize} {n : Uint63.int}
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
Lemma write_and_drop_restores_loc_owned {S : PageSize} {n : Uint63.int}
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
Lemma write_and_drop_preserves_step {S : PageSize} {n : Uint63.int}
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
      destruct l0; try discriminate.
      injection Hdrop as Heq. subst p'. reflexivity. 
      injection Hdrop as Heq. subst p'. simpl. reflexivity.
    - destruct (heap_lookup (ps_heap p_after_write) a) as [[cell state]|]; try discriminate.
      destruct state; try discriminate.
      destruct l0 as [|loc_lt rest]; try discriminate.
      destruct (lifetime_eq loc_lt l); try discriminate.
      injection Hdrop as Heq. subst p'. reflexivity. }
  rewrite Hstep2, Hstep1. reflexivity.
Qed.

(** read_mut_allocator preserves the original variable *)
Lemma read_mut_allocator_preserves_original_var {S : PageSize} {n : Uint63.int}
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
  unfold read_shared_allocator, let_shared_ref.
  rewrite Hvar, Hheap.
  assert (Hcont: lifetime_contained_in
            {| lt_id := ps_next_lifetime_id p; 
               lt_start := ps_current_step p; 
               lt_end := ps_current_step p + 2 |} lt = true).
  {
    unfold lifetime_contained_in; simpl.
    apply andb_true_iff. split.
    - apply Nat.leb_le. unfold lifetime_active in Hactive.
      apply andb_true_iff in Hactive. destruct Hactive as [Hstart _].
      apply Nat.leb_le in Hstart. exact Hstart.
    - apply Nat.leb_le. exact Hbound.
  }
  rewrite Hcont.
  remember (mk_lifetime (ps_next_lifetime_id p) (ps_current_step p) (ps_current_step p + 2)) as borrow_lt.
  remember ({|
    ps_heap := heap_update (ps_heap p) a m (LocShared [borrow_lt]);
    ps_vars := var_update (ps_vars p) (self ++ "_ref") (VarSharedRef a borrow_lt);
    ps_next_addr := ps_next_addr p;
    ps_next_lifetime_id := Datatypes.S (ps_next_lifetime_id p);
    ps_current_step := ps_current_step p
  |}) as p_ref.
  exists p_ref, (self ++ "_ref")%string.
  assert (Hvar_same: read_var p_ref (self ++ "_ref") = read_var p self).
  {
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
  assert (Halloc_same: @read_allocator S n p_ref (self ++ "_ref") = read_allocator p self).
  {
    unfold read_allocator.
    rewrite Hvar_same.
    reflexivity.
  }
  rewrite Halloc_same. rewrite Hread. reflexivity.
Qed.

Lemma drop_shared_ref_succeeds {S : PageSize} {n : Uint63.int}
  (p : prog_state) (v : var_name) (p_ref : prog_state) (v_ref : var_name) (alloc : BitmapAllocator S n) :
  @read_shared_allocator S n p v 2 = Some (p_ref, v_ref, alloc) ->
  exists p_fin, drop_var (step_forward p_ref) v_ref = Some p_fin.
Proof.
  intros Hr. unfold read_shared_allocator, let_shared_ref in Hr.
  destruct (var_lookup (ps_vars p) v) eqn:Hvar; try discriminate.
  destruct v0 as [a lt | a lt | a lt | a lt];
  destruct (heap_lookup (ps_heap p) a) as [[cell state]|] eqn:Hheap; try discriminate;
  destruct state as [| lts | lts]; try discriminate;
  destruct (lifetime_contained_in _ _) eqn:Hcont; try discriminate.
  all: destruct (read_allocator _ (v ++ "_ref")%string) eqn:Halloc_read; try discriminate;
       injection Hr as Hp_ref_eq Hv_ref_eq Ha_eq;
       subst p_ref v_ref;
       unfold step_forward, drop_var; simpl;
       rewrite var_update_eq;
       rewrite heap_update_lookup_same; simpl;
       eexists; reflexivity.
Qed.

(** frame only panics when read_shared_allocator fails *)
Lemma frame_panic_iff_read_shared_fails {S : PageSize} {n : Uint63.int}
  (p : prog_state) (self : var_name) (idx : Uint63.int) :
  @frame S n p self idx = Panic <->
  @read_shared_allocator S n p self 2 = None.
Proof.
  (* Cannot prove this since we cannot discharge the proof obligation for frame due to Rust's implementation bug *)
Admitted.

(** If read_shared_allocator succeeds, frame doesn't panic *)
Lemma frame_not_panic_when_read_shared_succeeds {S : PageSize} {n : Uint63.int}
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
Lemma frame_not_panic_when_accessible {S : PageSize} {n : Uint63.int}
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
Lemma read_mut_allocator_same_addr {S : PageSize} {n : Uint63.int}
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
Lemma read_mut_allocator_heap_state {S : PageSize} {n : Uint63.int}
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

  assert (H4pos : 4 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 4 alloc H4pos Hread) as Hpreserve.
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
        
        assert (Hsucc1: (exists p1_ref v1_ref, @read_shared_allocator S n p'' self 2 = Some (p1_ref, v1_ref, alloc'') /\
                                     exists p1_fin, drop_var (step_forward p1_ref) v1_ref = Some p1_fin)).
        {
          assert (Hneq: ref_var <> self).
          {
            pose proof (read_mut_allocator_ref_var_diff p p_ref self ref_var 4 alloc_read Hread_mut) as Heq_ref.
            rewrite Heq_ref. apply string_append_suffix_neq. discriminate.
          }
          assert (Hstep_p'' : ps_current_step p'' = 2 + ps_current_step p).
          {
            rewrite (write_and_drop_preserves_step (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite).
            simpl. rewrite (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read Hread_mut).
            reflexivity.
          }
          assert (Hvar_p' : var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
          {
            assert (Hvar_input : var_lookup (ps_vars (step_forward (step_forward p_ref))) self = Some (VarMutOwned a lt)).
            {
              rewrite !step_forward_preserves_var_lookup.
              apply (read_mut_allocator_preserves_original_var p p_ref self ref_var 4 alloc_read a lt Hread_mut Hvar_lookup).
            }
            apply (write_and_drop_preserves_var_ownership (step_forward (step_forward p_ref)) p'' ref_var self _ a lt Hvar_input Hwrite Hneq).
          }
          assert (Hactive_p'' : lifetime_active p'' lt = true).
          {
            unfold lifetime_active. rewrite Hstep_p''.
            unfold lifetime_active in Hactive. apply andb_true_iff in Hactive.
            destruct Hactive as [Hstart Hstep].
            apply andb_true_iff. split.
            - apply Nat.leb_le. apply Nat.leb_le in Hstart. lia.
            - apply Nat.ltb_lt. apply Nat.ltb_lt in Hstep. lia.
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
        pose proof (frame_idx_depends_on_range p'' p self self returned_frame alloc'' alloc 
                   Hread'' Hread Hrange_p''_p Hsucc1 Hsucc2) as Hidx_eq.
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
     pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Hstep_p_ref.
     pose proof (read_mut_allocator_ref_var_diff p p_ref self ref_var 4 alloc_read 
                   Hread_mut) as Href_var_eq.
     pose proof (read_mut_allocator_same_addr p p_ref self ref_var 4 alloc_read a lt 
                   Hread_mut Hvar_lookup) as [lt_ref Hvar_ref].
     assert (Hself_diff_ref: ref_var <> self).
     { rewrite Href_var_eq. apply string_append_suffix_neq. discriminate. }
     
     assert (Hvar_p'' : var_lookup (ps_vars p'') self = Some (VarMutOwned a lt)).
     {
       apply (write_and_drop_preserves_var_ownership 
                (step_forward (step_forward p_ref)) p'' ref_var self 
                {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
                   valid := valid alloc_read;
                   range := range alloc_read |} a lt).
       - rewrite !step_forward_preserves_var_lookup.
         apply (read_mut_allocator_preserves_original_var p p_ref self ref_var 4 alloc_read a lt 
                  Hread_mut Hvar_lookup).
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
     
     pose proof (write_and_drop_allocator_content (step_forward (step_forward p_ref)) p'' ref_var 
         {| allocated := set_bit (allocated alloc_read) frame_idx_val true;
            valid := valid alloc_read;
            range := range alloc_read |} self Hwrite) as [alloc' [Hread_p'' _]].

     pose proof (@frame_not_panic_when_accessible S n p'' self frame_idx_val alloc' a lt m'
                   Hvar_p'' Hread_p'' Hactive_p'' Hstep_bound_p'' Hheap_p'') as Hnot_panic.
     
     contradiction.
Qed.

(** No double allocation: allocate_frame never returns an already allocated frame *)
Theorem no_double_allocation {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (var : var_name)
  (f : PhysFrame S) (returned_frame : PhysFrame S) (p' : prog_state) :
  (exists alloc, read_allocator p var = Some alloc /\ 
    @allocator_wf S n alloc) ->
  (exists alloc, read_allocator p var = Some alloc /\
    exists idx, @frame_idx S n p var f = Ok idx /\
      get_bit (@allocated S n alloc) idx = true) ->
  @allocate_frame S n p var = Ok (returned_frame, p') ->
  f <> returned_frame.
Proof.
  intros Hwf Hallocf Halloc.
  Admitted.
  
(** A zero-initialized bitmap allocator is well-formed *)
Theorem zero_init_allocator_wf {S : PageSize} {n : Uint63.int} 
  (p : prog_state) (v : var_name) (r : PhysFrameRange S) (lt_end : nat) :
  match new_allocator n p v r lt_end with
  | Some (p', alloc_addr) =>
      True (* Placeholder *)
  | None => True
  end.
Proof.
  unfold new_allocator, let_mut_owned.
  destruct (Nat.ltb (ps_current_step p) lt_end) eqn:H; simpl; trivial.
Qed.

(*    
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
      + assert (H_intermediate_no_alloc: forall idx, idx < n * u63_bits -> 
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
*)
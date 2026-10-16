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
  unfold get_bit, make_bitarray.
  set (total_bits := Uint63.to_nat n * u64_bits).
  destruct (Uint63.to_nat idx <? total_bits)%nat eqn:Hlt.
  - rewrite Z_to_bv_small.
    + apply Z.testbit_0_l.
    + split; [lia |].
      unfold bv_modulus. simpl.
      rewrite Z_of_N_of_nat.
      apply Nat.ltb_lt in Hlt.
      pose proof (bitarray_fits_uint63 n) as Hfits.
      unfold total_bits in *.
      lia.
  - reflexivity.
Qed.

(** No frame is currently allocated *)
Definition allocated_clear {S : PageSize} {n : Uint63.int}
    (alloc : BitmapAllocator S n) : Prop :=
  forall idx, get_bit (allocated alloc) idx = false.

Lemma allocated_clear_wf {S : PageSize} {n : Uint63.int}
    (alloc : BitmapAllocator S n) :
  allocated_clear alloc -> allocator_wf alloc.
Proof.
  intros Hclear idx _ Halloc. rewrite Hclear in Halloc. discriminate.
Qed.

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
  intros Hbound.
  unfold new_allocator.
  destruct (let_mut_owned p var (@VAllocator S n (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r)) lt_end_param)
    as [[p' a']|] eqn:Hlet.
  - unfold let_mut_owned in Hlet.
    destruct (ps_current_step p <? lt_end_param)%nat eqn:Hlt; [| discriminate].
    injection Hlet as Hp' Ha'. subst p' a'.
    apply Nat.ltb_lt in Hlt.
    exists (ps_next_addr p),
           (mk_lifetime (ps_next_lifetime_id p) (ps_current_step p) lt_end_param),
           (mk_cell (@VAllocator S n (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r))).
    simpl.
    repeat split.
    + apply var_update_eq.
    + unfold lifetime_active. simpl.
      replace (ps_current_step p <=? ps_current_step p)%nat with true
        by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? lt_end_param)%nat with true
        by (symmetry; apply Nat.ltb_lt; lia).
      reflexivity.
    + simpl. lia.
    + apply heap_update_lookup_same.
  - trivial.
Qed.

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
  intros Hbound Hvalid_idx Hwf.
  unfold allocator_wf in *.
  intros idx' Hbound' Halloc'.
  simpl in *.
  destruct (Uint63.eqb idx idx') eqn:Heqb.
  - apply Uint63.eqb_spec in Heqb. subst idx'. exact Hvalid_idx.
  - assert (Hneq: idx <> idx') by uint63_neq_of_eqb Heqb.
    rewrite get_bit_set_bit_diff in Halloc' by exact Hneq.
    exact (Hwf idx' Hbound' Halloc').
Qed.

(** Setting any bit to false preserves allocator_wf **)
Lemma allocator_wf_set_allocated_false {S : PageSize} {n : Uint63.int}
  (alloc : BitmapAllocator S n) (idx : Uint63.int) :
  allocator_wf alloc ->
  allocator_wf (mkBitmapAllocator
                  (set_bit (allocated alloc) idx false)
                  (valid alloc)
                  (range alloc)).
Proof.
  intros Hwf.
  unfold allocator_wf in *.
  intros idx' Hbound' Halloc'.
  simpl in *.
  destruct (Uint63.eqb idx idx') eqn:Heqb.
  - apply Uint63.eqb_spec in Heqb. subst idx'.
    rewrite get_bit_set_bit_same in Halloc' by exact Hbound'.
    discriminate.
  - assert (Hneq: idx <> idx') by uint63_neq_of_eqb Heqb.
    rewrite get_bit_set_bit_diff in Halloc' by exact Hneq.
    exact (Hwf idx' Hbound' Halloc').
Qed.

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
  unfold new_allocator.
  destruct (let_mut_owned p var (@VAllocator S n (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r)) lt_end)
    as [[p' a']|] eqn:Hlet.
  - unfold let_mut_owned in Hlet.
    destruct (ps_current_step p <? lt_end)%nat eqn:Hlt; [| discriminate].
    injection Hlet as Hp' Ha'. subst p' a'.
    assert (Hread : @read_allocator S n
              {| ps_heap := heap_update (ps_heap p) (ps_next_addr p)
                              (mk_cell (@VAllocator S n (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r)))
                              LocOwned;
                 ps_vars := var_update (ps_vars p) var
                              (VarMutOwned (ps_next_addr p)
                                (mk_lifetime (ps_next_lifetime_id p) (ps_current_step p) lt_end));
                 ps_next_addr := Datatypes.S (ps_next_addr p);
                 ps_next_lifetime_id := Datatypes.S (ps_next_lifetime_id p);
                 ps_current_step := ps_current_step p |}
              var
            = Some (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r)).
    {
      apply read_allocator_same.
      unfold read_var. simpl.
      rewrite var_update_eq.
      unfold lifetime_active. simpl.
      apply Nat.ltb_lt in Hlt.
      replace (ps_current_step p <=? ps_current_step p)%nat with true
        by (symmetry; apply Nat.leb_le; lia).
      replace (ps_current_step p <? lt_end)%nat with true
        by (symmetry; apply Nat.ltb_lt; assumption).
      simpl.
      rewrite heap_update_lookup_same.
      reflexivity.
    }
    exists (mkBitmapAllocator (make_bitarray n) (make_bitarray n) r).
    split.
    + exact Hread.
    + unfold allocator_wf. intros idx _ Halloc.
      simpl in Halloc.
      rewrite make_bitarray_get_bit_false in Halloc.
      discriminate.
  - trivial.
Qed.

(** ** fill with [true] preserves all bits that are already set *)
Lemma fill_true_preserves_set_bits {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  get_bit bits idx = true ->
  get_bit (@fill n bits start_idx end_idx true) idx = true.
Proof.
  intros Hbit.
  unfold fill.
  revert bits Hbit.
  generalize (map (fun k : nat => Uint63.of_Z (Z.of_nat k))
                  (seq start_idx
                     (if Nat.leb start_idx end_idx
                      then S (end_idx - start_idx)
                      else 0))).
  intro indices.
  induction indices as [| i rest IH]; intros bits Hbit.
  - simpl. exact Hbit.
  - simpl. apply IH.
    destruct (Uint63.eqb i idx) eqn:Heqb.
    + apply Uint63.eqb_spec in Heqb. subst.
      destruct (Uint63.to_nat idx <? Uint63.to_nat n * u64_bits)%nat eqn:Hb.
      * apply Nat.ltb_lt in Hb.
        rewrite get_bit_set_bit_same; [reflexivity | assumption].
      * apply Nat.ltb_ge in Hb.
        rewrite set_bit_bounds; [exact Hbit | exact Hb].
    + assert (Hneq : i <> idx) by uint63_neq_of_eqb Heqb.
      rewrite get_bit_set_bit_diff; [exact Hbit | exact Hneq].
Qed.

(** fill with false preserves bits that are already false **)
Lemma fill_false_preserves_false_bits {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  get_bit bits idx = false ->
  get_bit (@fill n bits start_idx end_idx false) idx = false.
Proof.
  intros Hbit.
  unfold fill.
  revert bits Hbit.
  generalize (map (fun k : nat => Uint63.of_Z (Z.of_nat k))
                  (seq start_idx
                     (if Nat.leb start_idx end_idx
                      then S (end_idx - start_idx)
                      else 0))).
  intro indices.
  induction indices as [| i rest IH]; intros bits Hbit.
  - simpl. exact Hbit.
  - simpl. apply IH.
    destruct (Uint63.eqb i idx) eqn:Heqb.
    + apply Uint63.eqb_spec in Heqb. subst.
      destruct (Uint63.to_nat idx <? Uint63.to_nat n * u64_bits)%nat eqn:Hb.
      * apply Nat.ltb_lt in Hb.
        rewrite get_bit_set_bit_same; [reflexivity | assumption].
      * apply Nat.ltb_ge in Hb.
        rewrite set_bit_bounds; [exact Hbit | exact Hb].
    + assert (Hneq : i <> idx) by uint63_neq_of_eqb Heqb.
      rewrite get_bit_set_bit_diff; [exact Hbit | exact Hneq].
Qed.

Lemma fold_left_set_false_neq {n : Uint63.int}
    (indices : list Uint63.int) (idx : Uint63.int) :
  (forall i, In i indices -> Uint63.eqb i idx = false) ->
  forall (init : BitArray n),
  get_bit (fold_left (fun acc j => set_bit acc j false) indices init) idx
  = get_bit init idx.
Proof.
  intro Hall.
  induction indices as [|hd tl IH].
  - intro init. simpl. reflexivity.
  - intro init. simpl.
    rewrite IH.
    + assert (Hneq : hd <> idx).
      { intro Heq. subst.
        assert (Hhd_in : In idx (idx :: tl)) by (left; reflexivity).
        specialize (Hall idx Hhd_in).
        rewrite Uint63.eqb_refl in Hall. discriminate. }
      rewrite get_bit_set_bit_diff; [reflexivity | exact Hneq].
    + intros i Hin. apply Hall. right. exact Hin.
Qed.

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
  intros [alloc [Hread Hwf]] Hprecond.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  unfold mark_valid.

  destruct (@read_mut_allocator S n p self 6) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { trivial. }

  assert (H6pos : 6 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 6 alloc H6pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq [Hvalid_eq Hrange_eq]].
  assert (Heq_alloc : alloc_read = alloc).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.

  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].

  destruct (@frame_idx S n p_ref ref_var (start_frame S frame_range)) as [start_idx| |];
  destruct (@frame_idx S n p_ref ref_var (end_frame S frame_range))   as [end_idx  | |];
  simpl; try trivial.

  ok_branch p'' Hwrite.

  set (new_valid := @fill n (valid alloc)
                       (Z.to_nat (Uint63.to_Z start_idx))
                       (Z.to_nat (Uint63.to_Z end_idx))
                       true).

  assert (Hvar_ss : var_lookup (ps_vars (step_forward (step_forward p_ref))) self
                    = Some (VarMutOwned a lt)).
  { autorewrite with oak_step. exact Hvar_pref. }

  assert (Hactive_ss : lifetime_active (step_forward (step_forward p_ref)) lt = true).
  { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }

  assert (Href_ss : exists lt_ref,
            var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var
              = Some (VarMutRef a lt_ref) /\
            exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a
              = Some (cell, LocMut [lt_ref])).
  { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
    exists lt_ref. split.
    - autorewrite with oak_step. exact Hvar_ref.
    - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }

  pose proof (write_and_drop_allocator_content
                (step_forward (step_forward p_ref)) p'' ref_var self
                (mkBitmapAllocator (allocated alloc) new_valid (range alloc))
                a lt Hwrite Hvar_ss Hactive_ss Href_ss Hneq)
    as [alloc'' [Hread'' [Halloc'' [Hvalid'' _]]]].

  exists alloc''. split.
  - exact Hread''.
  - unfold allocator_wf. intros idx Hidx_bound Halloc_idx.
    rewrite Hvalid''. simpl.
    apply fill_true_preserves_set_bits.
    apply (Hwf idx Hidx_bound).
    simpl in Halloc''.
    rewrite Halloc'' in Halloc_idx. simpl in Halloc_idx.
    exact Halloc_idx.
Qed.

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
  intros Hprecond.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  unfold mark_valid.

  destruct (@read_mut_allocator S n p self 6) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { trivial. }

  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc_read a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].

  destruct (@frame_idx S n p_ref ref_var (start_frame S frame_range)) as [start_idx| |];
  destruct (@frame_idx S n p_ref ref_var (end_frame S frame_range))   as [end_idx  | |];
  simpl; try trivial.

  ok_branch p'' Hwrite.

  assert (Hvar_ss : var_lookup (ps_vars (step_forward (step_forward p_ref))) self
                    = Some (VarMutOwned a lt)).
  { autorewrite with oak_step. exact Hvar_pref. }

  assert (Hactive_ss : lifetime_active (step_forward (step_forward p_ref)) lt = true).
  { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }

  assert (Href_ss : exists lt_ref,
            var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var
              = Some (VarMutRef a lt_ref) /\
            exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a
              = Some (cell, LocMut [lt_ref])).
  { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
    exists lt_ref. split.
    - autorewrite with oak_step. exact Hvar_ref.
    - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }

  destruct Href_ss as [lt_ref [Hlookup_ref [cell_ref Hheap_ref]]].

  pose proof (write_and_drop_preserves_var_ownership
                (step_forward (step_forward p_ref)) p'' ref_var self _ a lt
                Hvar_ss Hwrite Hneq) as Hvar_p''.

  pose proof (write_and_drop_restores_loc_owned
                (step_forward (step_forward p_ref)) p'' ref_var _
                a Hwrite
                (ex_intro _ lt_ref Hlookup_ref)
                (ex_intro _ lt_ref (ex_intro _ cell_ref Hheap_ref)))
    as Hheap_p''.

  pose proof (write_and_drop_preserves_step
                (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite) as Hstep_p''.

  eexists a, lt, _.
  repeat split.
  - exact Hvar_p''.
  - pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 6 alloc_read Hread_mut)
      as Hstep_ref_eq.
    unfold lifetime_active in Hactive |- *.
    simpl in Hstep_p'' |- *.
    rewrite Hstep_p''. simpl.
    rewrite Hstep_ref_eq.
    apply andb_true_iff in Hactive. destruct Hactive as [Hs He].
    apply andb_true_iff. split.
    + apply Nat.leb_le. apply Nat.leb_le in Hs. lia.
    + apply Nat.ltb_lt. apply Nat.ltb_lt in He. lia.
  - pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 6 alloc_read Hread_mut)
      as Hstep_ref_eq.
    unfold step_forward in Hstep_p''. simpl in Hstep_p''.
    lia.
  - exact Hheap_p''.
Qed.

(** ** fill false is identity outside its range, provided end_idx < wB **)  
Lemma fill_false_identity_outside {n : Uint63.int}
    (bits : BitArray n) (start_idx end_idx : nat) (idx : Uint63.int) :
  (end_idx < Z.to_nat Uint63.wB)%nat ->
  (Uint63.to_nat idx < start_idx \/ end_idx < Uint63.to_nat idx)%nat ->
  get_bit (@fill n bits start_idx end_idx false) idx = get_bit bits idx.
Proof.
  intros Hwb_bound Hout.
  unfold fill.
  apply fold_left_set_false_neq.
  intros i Hin.
  apply in_map_iff in Hin.
  destruct Hin as [k [Hi_eq Hk_in]].
  simpl in Hi_eq.
  apply in_seq in Hk_in.
  destruct (Uint63.eqb i idx) eqn:Heqb; [| reflexivity].
  exfalso.
  apply Uint63.eqb_spec in Heqb.
  rewrite Heqb in Hi_eq.
  pose proof (f_equal Uint63.to_Z Hi_eq) as HkZ.
  rewrite Uint63.of_Z_spec in HkZ.
  destruct Hk_in as [Hk_lo Hk_hi].
  destruct (Nat.leb start_idx end_idx) eqn:Hle.
  - apply Nat.leb_le in Hle.
    assert (Hk_lt_wB : k < Z.to_nat Uint63.wB) by lia.
    assert (HkZ_small : (Z.of_nat k < Uint63.wB)%Z).
    { apply Nat2Z.inj_lt in Hk_lt_wB.
      rewrite Z2Nat.id in Hk_lt_wB by (unfold Uint63.wB; simpl; lia).
      exact Hk_lt_wB. }
    rewrite Z.mod_small in HkZ by lia.
    assert (Hto_nat : Uint63.to_nat idx = k).
    { unfold Uint63.to_nat. rewrite <- HkZ. apply Nat2Z.id. }
    destruct Hout as [Hlt | Hgt]; lia.
  - simpl in Hk_hi. lia.
Qed.

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
  intros [[alloc [Hread Hclear]]
          [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]]].
  unfold mark_valid.
  destruct (@read_mut_allocator S n p self 6) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { trivial. }
  assert (H6pos : 6 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 6 alloc H6pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq [Hvalid_eq Hrange_eq]].
  assert (Heq_alloc : alloc_read = alloc).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.
  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].
  destruct (@frame_idx S n p_ref ref_var (start_frame S r)) as [start_idx| |];
  destruct (@frame_idx S n p_ref ref_var (end_frame S r))   as [end_idx  | |];
  simpl; try trivial.
  ok_branch p'' Hwrite.
  set (new_valid := @fill n (valid alloc)
                       (Z.to_nat (Uint63.to_Z start_idx))
                       (Z.to_nat (Uint63.to_Z end_idx))
                       b).
  assert (Hvar_ss : var_lookup (ps_vars (step_forward (step_forward p_ref))) self
                    = Some (VarMutOwned a lt)).
  { autorewrite with oak_step. exact Hvar_pref. }
  assert (Hactive_ss : lifetime_active (step_forward (step_forward p_ref)) lt = true).
  { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }
  assert (Href_ss : exists lt_ref,
            var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var
              = Some (VarMutRef a lt_ref) /\
            exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a
              = Some (cell, LocMut [lt_ref])).
  { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
    exists lt_ref. split.
    - autorewrite with oak_step. exact Hvar_ref.
    - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }
  pose proof (write_and_drop_allocator_content
                (step_forward (step_forward p_ref)) p'' ref_var self
                (mkBitmapAllocator (allocated alloc) new_valid (range alloc))
                a lt Hwrite Hvar_ss Hactive_ss Href_ss Hneq)
    as [alloc'' [Hread'' [Halloc'' [Hvalid'' Hrange'']]]].
  split.
  - exists alloc''. split.
    + exact Hread''.
    + intros idx. rewrite Halloc''. cbn [allocated]. apply Hclear.
  - destruct Href_ss as [lt_ref [Hlookup_ref [cell_ref Hheap_ref]]].
    pose proof (write_and_drop_preserves_var_ownership
                  (step_forward (step_forward p_ref)) p'' ref_var self _ a lt
                  Hvar_ss Hwrite Hneq) as Hvar_p''.
    pose proof (write_and_drop_restores_loc_owned
                  (step_forward (step_forward p_ref)) p'' ref_var _
                  a Hwrite
                  (ex_intro _ lt_ref Hlookup_ref)
                  (ex_intro _ lt_ref (ex_intro _ cell_ref Hheap_ref)))
      as Hheap_p''.
    pose proof (write_and_drop_preserves_step
                  (step_forward (step_forward p_ref)) p'' ref_var _ Hwrite) as Hstep_p''.
    pose proof (read_mut_allocator_preserves_step p p_ref self ref_var 6 alloc Hread_mut)
      as Hstep_ref_eq.
    exists a, lt; eexists; repeat split.
    + exact Hvar_p''.
    + unfold lifetime_active in Hactive |- *.
      simpl in Hstep_p'' |- *.
      rewrite Hstep_p''. simpl. rewrite Hstep_ref_eq.
      apply andb_true_iff in Hactive. destruct Hactive as [Hs He].
      apply andb_true_iff. split.
      * apply Nat.leb_le. apply Nat.leb_le in Hs. lia.
      * apply Nat.ltb_lt. apply Nat.ltb_lt in He. lia.
    + unfold step_forward in Hstep_p''. simpl in Hstep_p''. lia.
    + exact Hheap_p''.
Qed.

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
  intros Hwb_bound Hnot_alloc Hwf.
  unfold allocator_wf in *.
  intros idx Hbound Halloc_idx.
  simpl in *.
  destruct (Nat.leb start_idx (Uint63.to_nat idx) &&
            Nat.leb (Uint63.to_nat idx) end_idx)%nat eqn:Hrange.
  - apply andb_true_iff in Hrange.
    destruct Hrange as [Hlo_b Hhi_b].
    apply Nat.leb_le in Hlo_b, Hhi_b.
    rewrite (Hnot_alloc idx (conj Hlo_b Hhi_b)) in Halloc_idx. discriminate.
  - apply andb_false_iff in Hrange.
    assert (Hout : (Uint63.to_nat idx < start_idx \/ end_idx < Uint63.to_nat idx)%nat).
    { destruct Hrange as [Hlo | Hhi].
      - left. apply Nat.leb_nle in Hlo. lia.
      - right. apply Nat.leb_nle in Hhi. lia. }
    rewrite (fill_false_identity_outside _ _ _ _ Hwb_bound Hout).
    exact (Hwf idx Hbound Halloc_idx).
Qed.

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
  induction rs as [|rv rest IH]; intros acc Hacc.
  - exact Hacc.
  - cbn [fold_left]. apply IH.
    destruct acc as [p | |]; [| exact I | exact I].
    pose proof (@mark_valid_step S n p self (fst rv) (snd rv) (2 * length rest)) as Hstep.
    replace (8 + 2 * length rest) with (6 + 2 * length (rv :: rest)) in Hstep
      by (cbn [length]; lia).
    exact (Hstep Hacc).
Qed.

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
  intros [alloc [Hread Hwf]] Hprecond Hframe_precond.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  destruct Hframe_precond as [fidx_pre [Hfidx_pre [alloc_f [Hread_f Halloc_pre]]]].
  rewrite Hread in Hread_f. injection Hread_f as Hread_f. subst alloc_f.

  pose proof (@deallocate_frame_correctness S n p self frame
                (ex_intro _ alloc (conj Hread Hwf))
                (ex_intro _ a (ex_intro _ lt (ex_intro _ m
                   (conj Hvar_lookup (conj Hactive (conj Hstep_bound Hheap))))))
                (ex_intro _ fidx_pre (conj Hfidx_pre (ex_intro _ alloc (conj Hread Halloc_pre)))))
    as Hcorr.

  unfold deallocate_frame in *.
  destruct (read_mut_allocator p self _) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { simpl in Hcorr. exact Hcorr. }

  assert (H6pos : 6 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 6 alloc H6pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq [Hvalid_eq Hrange_eq]].
  assert (Heq_alloc: alloc_read = alloc).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.

  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].

  destruct (@frame_idx S n p_ref ref_var frame) as [fidx| |] eqn:Hfidx.

  - destruct (negb (get_bit (valid alloc) fidx)) eqn:Hvalid_check.
    { simpl in Hcorr. exact Hcorr. }

    apply negb_false_iff in Hvalid_check.
    destruct (negb (get_bit (allocated alloc) fidx)) eqn:Halloc_check.
    { simpl in Hcorr. exact Hcorr. }

    apply negb_false_iff in Halloc_check.

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

    + simpl.
      pose proof (write_and_drop_allocator_content
                    (step_forward (step_forward (step_forward (step_forward p_ref)))) p'' ref_var self
                    {| allocated := set_bit (allocated alloc) fidx false;
                       valid := valid alloc;
                       range := range alloc |} a lt Hwrite Hvar_input Hactive_input Href_input Hneq)
        as [alloc' [Hread' [Halloc' [Hvalid' Hrange']]]].

      exists alloc'. split.
      * exact Hread'.
      * assert (Hwf' : allocator_wf {| allocated := set_bit (allocated alloc) fidx false;
                                       valid := valid alloc;
                                       range := range alloc |}).
        { apply allocator_wf_set_allocated_false. exact Hwf. }
        unfold allocator_wf in *.
        intros idx' Hidx'_bound Halloc_idx'.
        simpl in *.
        rewrite Hvalid'.
        apply (Hwf' idx' Hidx'_bound).
        simpl.
        rewrite <- Halloc'. exact Halloc_idx'.

    + trivial.

    + unfold write_and_drop in Hwrite.
      destruct (write_var _ _ _) as [p_after_write|] eqn:Hwrite_var.
      * destruct (drop_var _ _) as [p_final|] eqn:Hdrop; discriminate Hwrite.
      * discriminate Hwrite.

  - simpl in Hcorr. exact Hcorr.

  - simpl in Hcorr. exact Hcorr.
Qed.

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
  intros [alloc [Hread Hwf]] Hprecond Hno_alloc.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].
  unfold mark_valid.

  destruct (@read_mut_allocator S n p self 6) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { trivial. }

  assert (H6pos : 6 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 6 alloc H6pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq [Hvalid_eq Hrange_eq]].
  assert (Heq_alloc : alloc_read = alloc).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.

  pose proof (read_mut_allocator_setup p p_ref self ref_var 6 alloc a lt m
                Hread_mut Hvar_lookup Hheap)
    as [Hneq [Hstep_pref [Hvar_pref Href_pref]]].

  destruct (@frame_idx S n p_ref ref_var (start_frame S frame_range)) as [start_idx| |] eqn:Hfidx_start;
  destruct (@frame_idx S n p_ref ref_var (end_frame S frame_range))   as [end_idx  | |] eqn:Hfidx_end;
  simpl; try trivial.

  ok_branch p'' Hwrite.

  set (new_valid := @fill n (valid alloc)
                       (Z.to_nat (Uint63.to_Z start_idx))
                       (Z.to_nat (Uint63.to_Z end_idx))
                       false).

  assert (Hvar_ss : var_lookup (ps_vars (step_forward (step_forward p_ref))) self
                    = Some (VarMutOwned a lt)).
  { autorewrite with oak_step. exact Hvar_pref. }

  assert (Hactive_ss : lifetime_active (step_forward (step_forward p_ref)) lt = true).
  { unfold lifetime_active. simpl. rewrite Hstep_pref. finish_lifetime_active Hactive. }

  assert (Href_ss : exists lt_ref,
            var_lookup (ps_vars (step_forward (step_forward p_ref))) ref_var
              = Some (VarMutRef a lt_ref) /\
            exists cell, heap_lookup (ps_heap (step_forward (step_forward p_ref))) a
              = Some (cell, LocMut [lt_ref])).
  { destruct Href_pref as [lt_ref [Hvar_ref [cell_ref Hheap_ref]]].
    exists lt_ref. split.
    - autorewrite with oak_step. exact Hvar_ref.
    - autorewrite with oak_step. exists cell_ref. exact Hheap_ref. }

  pose proof (write_and_drop_allocator_content
                (step_forward (step_forward p_ref)) p'' ref_var self
                (mkBitmapAllocator (allocated alloc) new_valid (range alloc))
                a lt Hwrite Hvar_ss Hactive_ss Href_ss Hneq)
    as [alloc'' [Hread'' [Halloc'' [Hvalid'' _]]]].

  exists alloc''. split.
  - exact Hread''.
  - assert (Hwf' : allocator_wf (mkBitmapAllocator (allocated alloc) new_valid (range alloc))).
    { apply allocator_wf_fill_valid_false.
      - unfold new_valid.
        pose proof (Uint63.to_Z_bounded end_idx) as [Hend_lo Hend_hi].
        assert (Hwb_nonneg : (0 <= Uint63.wB)%Z) by lia.
        exact (proj1 (Z2Nat.inj_lt _ _ Hend_lo Hwb_nonneg) Hend_hi).
      - intros idx Hrange_idx.
        exact (Hno_alloc p_ref ref_var alloc start_idx end_idx
                 eq_refl Hfidx_start Hfidx_end idx Hrange_idx).
      - exact Hwf. }
    unfold allocator_wf in *.
    intros idx Hidx_bound Halloc_idx.
    cbn [allocated valid] in *.
    rewrite Hvalid''.
    apply (Hwf' idx Hidx_bound).
    cbn [allocated valid]. rewrite <- Halloc''. exact Halloc_idx.
Qed.

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
  intros Hinv.
  pose proof (@init_fold_inv S n self ranges (Ok p) Hinv) as H.
  unfold init_allocator.
  destruct (fold_left _ ranges (Ok p)) as [p' | |] eqn:E;
    rewrite ?E in H; try exact I.
  destruct H as [[alloc' [Hread' Hclear']] _].
  exists alloc'. split; [exact Hread' | apply allocated_clear_wf; exact Hclear'].
Qed.

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
  intros [alloc [Hread Hwf]] Hprecond.
  destruct Hprecond as [a [lt [m [Hvar_lookup [Hactive [Hstep_bound Hheap]]]]]].

  assert (Hstep_bound4: ps_current_step p + 6 <= lt_end lt) by exact Hstep_bound.

  pose proof (@allocate_frame_correctness S n p self
                (ex_intro _ alloc (conj Hread Hwf))
                (ex_intro _ a (ex_intro _ lt (ex_intro _ m
                   (conj Hvar_lookup (conj Hactive (conj Hstep_bound Hheap)))))))
    as Hcorr.

  unfold allocate_frame in *.
  destruct (read_mut_allocator p self _) as [[[p_ref ref_var] alloc_read]|] eqn:Hread_mut.
  2: { simpl in Hcorr. exact Hcorr. }

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
         rewrite Hdrop' in Hdrop. discriminate. }

  simpl.
  destruct (write_and_drop _ _ _) as [p''| |] eqn:Hwrite.
  2: { trivial. }
  2: { exfalso.
       unfold write_and_drop in Hwrite.
       destruct (write_var _ _ _) as [p_after_write|] eqn:Hwrite_var.
       - destruct (drop_var _ _) as [p_final|] eqn:Hdrop; discriminate Hwrite.
       - discriminate Hwrite. }

  destruct (frame p'' self frame_idx_val) as [returned_frame| |] eqn:Hframe.
  2: { trivial. }
  2: { simpl in Hcorr. exact Hcorr. }

  simpl.

  simpl in Hcorr.
  destruct Hcorr as [_ [alloc' [Hread_p' _]]].

  assert (H4pos : 4 > 0) by lia.
  pose proof (read_mut_allocator_preserves_content p self 4 alloc H4pos Hread) as Hpres.
  rewrite Hread_mut in Hpres.
  destruct Hpres as [Halloc_eq [Hvalid_eq Hrange_eq]].
  assert (Heq_alloc: alloc = alloc_read).
  { destruct alloc, alloc_read; simpl in *; subst; reflexivity. }
  subst alloc_read.

  assert (Hframe_idx_bound: Uint63.to_nat frame_idx_val < to_nat n * u64_bits).
  { apply first_one_from_zero_lt with (bits := get_available (allocated alloc) (valid alloc)).
    exact Hfirst. }

  assert (Havailable: get_bit (get_available (allocated alloc) (valid alloc)) frame_idx_val = true).
  { apply first_one_returns_true. exact Hfirst. }

  unfold get_available in Havailable.
  rewrite bitand_get_bit in Havailable.
  apply andb_true_iff in Havailable.
  destruct Havailable as [Hvalid_bit Hnot_alloc_bit].
  rewrite bitnot_get_bit in Hnot_alloc_bit by exact Hframe_idx_bound.
  apply negb_true_iff in Hnot_alloc_bit.

  pose proof (read_mut_allocator_setup p p_ref self ref_var 4 alloc a lt m
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

  pose proof (write_and_drop_allocator_content
                (step_forward (step_forward p_ref)) p'' ref_var self
                {| allocated := set_bit (allocated alloc) frame_idx_val true;
                   valid := valid alloc;
                   range := range alloc |} a lt Hwrite Hvar_input Hactive_input Href_input Hneq)
    as [alloc'' [Hread'' [Halloc'' [Hvalid'' Hrange'']]]].

  exists alloc''.
  split.
  - rewrite Hread'' in Hread_p'.
    injection Hread_p' as Heq'. subst alloc'.
    exact Hread''.
  - assert (Hwf' : allocator_wf {| allocated := set_bit (allocated alloc) frame_idx_val true;
                                   valid := valid alloc;
                                   range := range alloc |}).
    { apply allocator_wf_set_allocated_true; assumption. }
    unfold allocator_wf in *.
    intros idx Hidx_bound Halloc_idx.
    simpl in *.
    rewrite Hvalid''.
    apply (Hwf' idx Hidx_bound).
    simpl.
    rewrite <- Halloc''. exact Halloc_idx.
Qed.

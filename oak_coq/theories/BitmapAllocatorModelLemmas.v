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
From OC Require Export BitmapAllocatorArith.

Local Open Scope string_scope.

Ltac finish_lifetime_active H :=
  unfold lifetime_active in H;
  apply andb_true_iff in H;
  let hs := fresh "Hlt_s" in
  let he := fresh "Hlt_e" in
  destruct H as [hs he];
  apply andb_true_iff; split;
  [ apply Nat.leb_le; apply Nat.leb_le in hs; lia
  | apply Nat.ltb_lt; apply Nat.ltb_lt in he; lia ].

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


(** [oak_step]: erase [step_forward] from a variable or heap lookup. *)
#[export] Hint Rewrite step_forward_preserves_var_lookup
                        step_forward_preserves_heap_lookup : oak_step.

(** [oak_update]: resolve a lookup that lands on the just-written entry. *)
#[export] Hint Rewrite var_update_eq heap_update_lookup_same : oak_update.

(** [oak_eqb]: collapse reflexive boolean equalities to [true]. *)
#[export] Hint Rewrite Nat.eqb_refl Uint63.eqb_refl String.eqb_refl : oak_eqb.

(** One call to discharge the common state-threading simplifications. *)
Ltac oak_state_simpl := autorewrite with oak_step oak_update oak_eqb in *.

(** Prove [a <> b] from [H : (a =? b)%uint63 = false]. *)
Ltac uint63_neq_of_eqb H :=
  let Heq := fresh "Heq" in
  intro Heq; rewrite Heq in H; rewrite Uint63.eqb_refl in H; discriminate.

Ltac ok_branch name H :=
  match goal with
  | [ |- context [ match ?t with Ok _ => _ | Err => _ | Panic => _ end ] ] =>
      destruct t as [name | | ] eqn:H; [ | trivial | trivial ]
  end.

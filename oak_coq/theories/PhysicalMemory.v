Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.

(** * Basic Types *)

Local Open Scope uint63_scope.

(** Physical address representation *)
Definition PhysAddr := Uint63.int.

(** Represents a page size *)
Record PageSize := mkPageSize {
  size : Uint63.int;
  size_positive : (0 <? size) = true
}.

(** A physical frame with a specific page size *)
Record PhysFrame (S : PageSize) := mkPhysFrame {
  start_address : PhysAddr;
  (* Ensure frame is properly aligned *)
  frame_aligned : (start_address mod (size S)) = 0
}.

(** A range of physical frames *)
Record PhysFrameRange (S : PageSize) := mkPhysFrameRange {
  start_frame : PhysFrame S;
  end_frame : PhysFrame S;
  (* Ensure start <= end *)
  range_valid : ((start_address S start_frame) <? (start_address S end_frame)) = true
}.

Lemma size_nonzero {S : PageSize} : 0 <> size S.
Proof.
  intro H.
  pose proof (size_positive S) as G.
  rewrite <- H in G.
  assert (H1: (0 <? 0) = false) by reflexivity.
  rewrite H1 in G.
  discriminate G.
Qed.

Definition ltb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.ltb a b.

Definition leb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.leb a b.

Definition eqb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.eqb a b.
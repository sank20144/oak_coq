Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Import ListNotations.

(** * Basic Types *)

(** Physical address representation *)
Definition PhysAddr := Z.

(** Represents a page size *)
Record PageSize := mkPageSize {
  size : Z;
  size_positive : Z.gt size 0
}.

(** A physical frame with a specific page size *)
Record PhysFrame (S : PageSize) := mkPhysFrame {
  start_address : PhysAddr;
  (* Ensure frame is properly aligned *)
  frame_aligned : (Z.modulo start_address (size S)) = 0%Z
}.

(** A range of physical frames *)
Record PhysFrameRange (S : PageSize) := mkPhysFrameRange {
  start_frame : PhysFrame S;
  end_frame : PhysFrame S;
  (* Ensure start <= end *)
  range_valid : Z.le (start_address S start_frame) (start_address S end_frame)
}.

Lemma size_nonzero {S : PageSize} : 0%Z <> size S.
Proof.
  intro H.
  pose proof (size_positive S) as G.
  rewrite H in G. 
  lia.
Qed.
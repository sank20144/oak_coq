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

(** Constructor for PhysAddr *)
Definition mkPhysAddr (addr : Uint63.int) : PhysAddr := addr.

(** Valid page sizes: 4KB or 2MB *)
Inductive ValidPageSize : Set :=
  | Page4KB : ValidPageSize
  | Page2MB : ValidPageSize.

(** Convert valid page size to actual size in bytes *)
Definition page_size_to_bytes (ps : ValidPageSize) : Uint63.int :=
  match ps with
  | Page4KB => 4096           (* 4KB *)
  | Page2MB => 512 * 4096     (* 2MB *)
  end.

(** Represents a page size constrained to valid sizes *)
Record PageSize := mkPageSize {
  page_type : ValidPageSize;
  size := page_size_to_bytes page_type;
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
  (* Ensure start < end *)
  range_valid : ((start_address S start_frame) <? (start_address S end_frame)) = true
}.

Lemma size_nonzero {S : PageSize} : 0%uint63 <> (size S)%uint63.
Proof.
  intro H.
  unfold size in H.
  destruct (page_type S) as [|].
  - simpl in H.
    apply (Uint63.eqb_false_spec 0 4096).
    reflexivity. exact H.
  - simpl in H.
    apply (Uint63.eqb_false_spec 0 2097152).
    reflexivity.
    exact H.
Qed.

Definition ltb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.ltb a b.

Definition leb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.leb a b.

Definition eqb_phys_addr (a b : PhysAddr) : bool :=
  Uint63.eqb a b.

Definition add_phys_addr (a b : PhysAddr) : Uint63.int :=
  Uint63.add a b.

Lemma PageSize_eq_dec : forall (s1 s2 : PageSize), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  decide equality.
Defined.
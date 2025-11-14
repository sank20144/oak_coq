Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.

(* Memory addresses *)
Definition addr := nat.

(* Values stored in memory - abstract type for now *)
Parameter value : Type.

(* Memory cell containing value and borrow state *)
Record mem_cell : Type := mk_cell {
  cell_value : value;
}.

Definition memory := list (addr * mem_cell).

(* Complete program state *)
Record program_state : Type := mk_memory {
  state_mem : memory;
  mem_next_addr : addr;
}.

(* Initial empty memory *)
Definition empty_memory : program_state := 
  mk_memory [] 0.

(* Lookup value in heap *)
Fixpoint heap_lookup (h : memory) (a : addr) : option mem_cell :=
  match h with
  | [] => None
  | (a', cell) :: h' => 
      if Nat.eqb a a' then Some cell 
      else heap_lookup h' a
  end.

(* Update heap at address *)
Fixpoint heap_update (h : memory) (a : addr) (cell : mem_cell) : memory :=
  match h with
  | [] => [(a, cell)]
  | (a', cell') :: h' =>
      if Nat.eqb a a' then (a, cell) :: h'
      else (a', cell') :: heap_update h' a cell
  end.

(* Allocate new value *)
Definition alloc (p : program_state) (v : value) : program_state * addr :=
  let a := mem_next_addr p in
  let cell := mk_cell v in
  let h' := heap_update (state_mem p) a cell in
  (mk_memory h'  (S a), a).


Definition read (p : program_state) (a : addr) : option value :=
  match heap_lookup (state_mem p) a with
  | None => None
  | Some cell => Some (cell_value cell)
  end.

Definition write (p : program_state) (a : addr) (v : value) : option program_state :=
  match heap_lookup (state_mem p) a with
  | None => None
  | Some cell =>
      let cell' := mk_cell v in
      let h' := heap_update (state_mem p) a cell' in
      Some (mk_memory h' (mem_next_addr p))
  end.


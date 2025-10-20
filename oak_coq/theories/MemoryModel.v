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

(* Lifetimes represented as natural numbers *)
Definition lifetime := nat.

(* Values stored in memory - abstract type for now *)
Parameter value : Type.

(* Borrow state for a memory location *)
Inductive borrow_state : Type :=
  | Owned : borrow_state                      (* No active borrows *)
  | SharedBorrowed : list lifetime -> borrow_state  (* Multiple shared borrows *)
  | MutBorrowed : lifetime -> borrow_state.   (* Single mutable borrow *)

(* Memory cell containing value and borrow state *)
Record mem_cell : Type := mk_cell {
  cell_value : value;
  cell_state : borrow_state
}.

(* Heap is a partial map from addresses to memory cells *)
Definition heap := list (addr * mem_cell).

(* Borrow tracking - maps lifetimes to borrowed addresses *)
Definition borrow_map := list (lifetime * addr).

(* Complete memory state *)
Record memory : Type := mk_memory {
  mem_heap : heap;
  mem_borrows : borrow_map;
  mem_next_addr : addr;
  mem_next_lifetime : lifetime
}.

(* Initial empty memory *)
Definition empty_memory : memory := 
  mk_memory [] [] 0 0.

(* Lookup value in heap *)
Fixpoint heap_lookup (h : heap) (a : addr) : option mem_cell :=
  match h with
  | [] => None
  | (a', cell) :: h' => 
      if Nat.eqb a a' then Some cell 
      else heap_lookup h' a
  end.

(* Update heap at address *)
Fixpoint heap_update (h : heap) (a : addr) (cell : mem_cell) : heap :=
  match h with
  | [] => [(a, cell)]
  | (a', cell') :: h' =>
      if Nat.eqb a a' then (a, cell) :: h'
      else (a', cell') :: heap_update h' a cell
  end.

(* Check if borrow is valid *)
Definition can_borrow_shared (bs : borrow_state) : bool :=
  match bs with
  | Owned => true
  | SharedBorrowed _ => true
  | MutBorrowed _ => false
  end.

Definition can_borrow_mut (bs : borrow_state) : bool :=
  match bs with
  | Owned => true
  | _ => false
  end.

(* Allocate new value in memory *)
Definition alloc (m : memory) (v : value) : memory * addr :=
  let a := mem_next_addr m in
  let cell := mk_cell v Owned in
  let h' := heap_update (mem_heap m) a cell in
  (mk_memory h' (mem_borrows m) (S a) (mem_next_lifetime m), a).

(* Create shared borrow *)
Definition borrow_shared (m : memory) (a : addr) : option (memory * lifetime) :=
  match heap_lookup (mem_heap m) a with
  | None => None
  | Some cell =>
      if can_borrow_shared (cell_state cell) then
        let lt := mem_next_lifetime m in
        let new_state := match cell_state cell with
                        | Owned => SharedBorrowed [lt]
                        | SharedBorrowed lts => SharedBorrowed (lt :: lts)
                        | MutBorrowed _ => Owned (* unreachable | check again *)
                        end in
        let cell' := mk_cell (cell_value cell) new_state in
        let h' := heap_update (mem_heap m) a cell' in
        let borrows' := (lt, a) :: mem_borrows m in
        Some (mk_memory h' borrows' (mem_next_addr m) (S lt), lt)
      else None
  end.

(* Create mutable borrow *)
Definition borrow_mut (m : memory) (a : addr) : option (memory * lifetime) :=
  match heap_lookup (mem_heap m) a with
  | None => None
  | Some cell =>
      if can_borrow_mut (cell_state cell) then
        let lt := mem_next_lifetime m in
        let cell' := mk_cell (cell_value cell) (MutBorrowed lt) in
        let h' := heap_update (mem_heap m) a cell' in
        let borrows' := (lt, a) :: mem_borrows m in
        Some (mk_memory h' borrows' (mem_next_addr m) (S lt), lt)
      else None
  end.

(* End a borrow (lifetime expires) *)
Fixpoint remove_lifetime (lts : list lifetime) (lt : lifetime) : list lifetime :=
  match lts with
  | [] => []
  | lt' :: lts' => if Nat.eqb lt lt' then lts' else lt' :: remove_lifetime lts' lt
  end.

Fixpoint remove_borrow (borrows : borrow_map) (lt : lifetime) : borrow_map :=
  match borrows with
  | [] => []
  | (lt', a) :: bs => if Nat.eqb lt lt' then bs else (lt', a) :: remove_borrow bs lt
  end.

Definition end_borrow (m : memory) (lt : lifetime) : option memory :=
  (* Find which address this lifetime borrowed *)
  let fix find_addr (borrows : borrow_map) : option addr :=
    match borrows with
    | [] => None
    | (lt', a) :: bs => if Nat.eqb lt lt' then Some a else find_addr bs
    end in
  match find_addr (mem_borrows m) with
  | None => None
  | Some a =>
      match heap_lookup (mem_heap m) a with
      | None => None
      | Some cell =>
          let new_state := match cell_state cell with
                          | MutBorrowed lt' => 
                              if Nat.eqb lt lt' then Owned else cell_state cell
                          | SharedBorrowed lts =>
                              let lts' := remove_lifetime lts lt in
                              if Nat.eqb (length lts') 0 then Owned else SharedBorrowed lts'
                          | Owned => Owned
                          end in
          let cell' := mk_cell (cell_value cell) new_state in
          let h' := heap_update (mem_heap m) a cell' in
          let borrows' := remove_borrow (mem_borrows m) lt in
          Some (mk_memory h' borrows' (mem_next_addr m) (mem_next_lifetime m))
      end
  end.

(* Read from memory location *)
Definition read (m : memory) (a : addr) : option value :=
  match heap_lookup (mem_heap m) a with
  | None => None
  | Some cell => Some (cell_value cell)
  end.

(* Write to memory location (requires ownership or mutable borrow) *)
Definition write (m : memory) (a : addr) (v : value) : option memory :=
  match heap_lookup (mem_heap m) a with
  | None => None
  | Some cell =>
      (* Can only write if owned or mutably borrowed *)
      match cell_state cell with
      | Owned => 
          let cell' := mk_cell v Owned in
          let h' := heap_update (mem_heap m) a cell' in
          Some (mk_memory h' (mem_borrows m) (mem_next_addr m) (mem_next_lifetime m))
      | MutBorrowed lt =>
          let cell' := mk_cell v (MutBorrowed lt) in
          let h' := heap_update (mem_heap m) a cell' in
          Some (mk_memory h' (mem_borrows m) (mem_next_addr m) (mem_next_lifetime m))
      | SharedBorrowed _ => None
      end
  end.


Definition no_dangling_refs (m : memory) : Prop :=
  forall lt a, In (lt, a) (mem_borrows m) -> 
    exists cell, heap_lookup (mem_heap m) a = Some cell.

(* No conflicting borrows *)
Definition valid_borrows (m : memory) : Prop :=
  forall a cell, heap_lookup (mem_heap m) a = Some cell ->
    match cell_state cell with
    | MutBorrowed lt => 
        (* Only one mutable borrow exists *)
        forall lt' a', In (lt', a') (mem_borrows m) -> a' = a -> lt' = lt
    | SharedBorrowed lts =>
        (* All shared borrows are tracked *)
        forall lt, In lt lts -> exists a', In (lt, a') (mem_borrows m)
    | Owned => True
    end.

(* Well-formed memory *)
Definition wf_memory (m : memory) : Prop :=
  no_dangling_refs m /\ valid_borrows m.
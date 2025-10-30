Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

(* Variable names *)
Definition var_name := string.

(* Memory addresses *)
Definition addr := nat.

(* Lifetime identifier *)
Definition lifetime_id := nat.

(* Lifetime with explicit scope bounds *)
Record lifetime : Type := mk_lifetime {
  lt_id : lifetime_id;
  lt_start : nat;  (* When this lifetime begins (program counter / step) *)
  lt_end : nat     (* When this lifetime ends (must be explicitly set) *)
}.

(* Abstract value type *)
Parameter value : Type.

(* Variable ownership status *)
Inductive var_ownership : Type :=
  | VarOwned : addr -> lifetime -> var_ownership        (* Owns value at address with lifetime *)
  | VarSharedRef : addr -> lifetime -> var_ownership    (* Shared reference to address *)
  | VarMutRef : addr -> lifetime -> var_ownership.      (* Mutable reference to address *)

(* Memory cell with value *)
Record mem_cell : Type := mk_cell {
  cell_value : value
}.

(* Borrow state for tracking active borrows on a location *)
Inductive location_state : Type :=
  | LocOwned : location_state                          (* No active borrows *)
  | LocShared : list lifetime -> location_state        (* Multiple shared borrows *)
  | LocMut : lifetime -> location_state.               (* Single mutable borrow *)

(* Heap stores values and their borrow states *)
Definition heap := list (addr * mem_cell * location_state).

(* Variable environment maps variable names to their ownership *)
Definition var_env := list (var_name * var_ownership).

(* Complete program state *)
Record prog_state : Type := mk_prog_state {
  ps_heap : heap;
  ps_vars : var_env;
  ps_next_addr : addr;
  ps_next_lifetime_id : lifetime_id;
  ps_current_step : nat  (* Current program step/time *)
}.

(* Initial empty state *)
Definition empty_state : prog_state :=
  mk_prog_state [] [] 0 0 0.

(* Helper: check if lifetime lt1 outlives lt2 (lt1's scope contains lt2's scope) *)
Definition lifetime_outlives (lt1 lt2 : lifetime) : bool :=
  (Nat.leb (lt_start lt1) (lt_start lt2)) && (Nat.leb (lt_end lt2) (lt_end lt1)).

(* Helper: check if a lifetime is contained within another *)
Definition lifetime_contained_in (inner outer : lifetime) : bool :=
  (Nat.leb (lt_start outer) (lt_start inner)) && (Nat.leb (lt_end inner) (lt_end outer)).

(* Helper: check if a lifetime is currently active *)
Definition lifetime_active (s : prog_state) (lt : lifetime) : bool :=
  (Nat.leb (lt_start lt) (ps_current_step s)) && (Nat.ltb (ps_current_step s) (lt_end lt)).

(* Helper: lookup variable *)
Fixpoint var_lookup (vars : var_env) (v : var_name) : option var_ownership :=
  match vars with
  | [] => None
  | (v', own) :: rest =>
      if String.eqb v v' then Some own else var_lookup rest v
  end.

(* Helper: lookup location in heap *)
Fixpoint heap_lookup (h : heap) (a : addr) : option (mem_cell * location_state) :=
  match h with
  | [] => None
  | (a', cell, state) :: rest =>
      if Nat.eqb a a' then Some (cell, state) else heap_lookup rest a
  end.

(* Helper: update heap *)
Fixpoint heap_update (h : heap) (a : addr) (cell : mem_cell) (state : location_state) : heap :=
  match h with
  | [] => [(a, cell, state)]
  | (a', cell', state') :: rest =>
      if Nat.eqb a a' then (a, cell, state) :: rest
      else (a', cell', state') :: heap_update rest a cell state
  end.

(* Helper: add/update variable *)
Fixpoint var_update (vars : var_env) (v : var_name) (own : var_ownership) : var_env :=
  match vars with
  | [] => [(v, own)]
  | (v', own') :: rest =>
      if String.eqb v v' then (v, own) :: rest
      else (v', own') :: var_update rest v own
  end.

(* Helper: remove variable from environment *)
Definition var_remove (vars : var_env) (v : var_name) : var_env :=
  filter (fun '(v', _) => negb (String.eqb v v')) vars.

(* Check if any borrows at address have lifetimes that outlive owner_lt *)
Definition has_outliving_borrows (h : heap) (a : addr) (owner_lt : lifetime) : bool :=
  match heap_lookup h a with
  | Some (_, LocShared lts) => 
      existsb (fun lt => negb (lifetime_contained_in lt owner_lt)) lts
  | Some (_, LocMut lt) => 
      negb (lifetime_contained_in lt owner_lt)
  | _ => false
  end.

(* Create an owned variable with a new value *)
(* The caller must provide the expected lifetime end *)
Definition let_owned (s : prog_state) (var : var_name) (val : value) (lt_end : nat)
    : option (prog_state * addr) :=
  if Nat.ltb (ps_current_step s) lt_end then
    let a := ps_next_addr s in
    let lt_id := ps_next_lifetime_id s in
    let lt := mk_lifetime lt_id (ps_current_step s) lt_end in
    let cell := mk_cell val in
    let h' := heap_update (ps_heap s) a cell LocOwned in
    let vars' := var_update (ps_vars s) var (VarOwned a lt) in
    Some (mk_prog_state h' vars' (S a) (S lt_id) (ps_current_step s), a)
  else None.  (* Invalid lifetime bounds *)

(* Create a shared reference: let ref_var = &owned_var *)
(* The borrow's lifetime must be contained within the owner's lifetime *)
Definition let_shared_ref (s : prog_state) (ref_var : var_name) (owned_var : var_name) (borrow_end : nat)
    : option prog_state :=
  match var_lookup (ps_vars s) owned_var with
  | Some (VarOwned a owner_lt) =>
      (* Check if location can be shared borrowed *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocOwned) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          (* Ensure borrow lifetime is contained within owner lifetime *)
          if lifetime_contained_in borrow_lt owner_lt then
            let h' := heap_update (ps_heap s) a cell (LocShared [borrow_lt]) in
            let vars' := var_update (ps_vars s) ref_var (VarSharedRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None  (* Borrow would outlive owner *)
      | Some (cell, LocShared lts) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          if lifetime_contained_in borrow_lt owner_lt then
            let h' := heap_update (ps_heap s) a cell (LocShared (borrow_lt :: lts)) in
            let vars' := var_update (ps_vars s) ref_var (VarSharedRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None
      | _ => None
      end
  | Some (VarSharedRef a ref_lt) =>
      (* Can reborrow from shared reference, but new borrow must be contained within source *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocShared lts) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          if lifetime_contained_in borrow_lt ref_lt then
            let h' := heap_update (ps_heap s) a cell (LocShared (borrow_lt :: lts)) in
            let vars' := var_update (ps_vars s) ref_var (VarSharedRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None
      | _ => None
      end
  | _ => None
  end.

(* Create a mutable reference: let ref_var = &mut owned_var *)
Definition let_mut_ref (s : prog_state) (ref_var : var_name) (owned_var : var_name) (borrow_end : nat)
    : option prog_state :=
  match var_lookup (ps_vars s) owned_var with
  | Some (VarOwned a owner_lt) =>
      (* Check if location can be mutably borrowed *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocOwned) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          (* Ensure borrow lifetime is contained within owner lifetime *)
          if lifetime_contained_in borrow_lt owner_lt then
            let h' := heap_update (ps_heap s) a cell (LocMut borrow_lt) in
            let vars' := var_update (ps_vars s) ref_var (VarMutRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None  (* Borrow would outlive owner *)
      | _ => None  (* Cannot mutably borrow if any borrows exist *)
      end
  | Some (VarMutRef a ref_lt) =>
      (* Can reborrow from mutable reference *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocMut _) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          (* New borrow must be contained within source reference *)
          if lifetime_contained_in borrow_lt ref_lt then
            let h' := heap_update (ps_heap s) a cell (LocMut borrow_lt) in
            let vars' := var_update (ps_vars s) ref_var (VarMutRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None
      | _ => None
      end
  | _ => None
  end.

(* Read through a variable *)
Definition read_var (s : prog_state) (var : var_name) : option value :=
  match var_lookup (ps_vars s) var with
  | Some (VarOwned a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocOwned) => Some (cell_value cell)
        | Some (cell, LocShared _) => Some (cell_value cell)  (* OK to read when shared borrowed *)
        | Some (cell, LocMut _) => None  (* Cannot read when mutably borrowed *)
        | None => None
        end
      else None  (* Lifetime expired *)
  | Some (VarSharedRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, _) => Some (cell_value cell)
        | None => None
        end
      else None
  | Some (VarMutRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, _) => Some (cell_value cell)
        | None => None
        end
      else None
  | None => None
  end.

(* Write through a variable (only owned or mut ref) *)
Definition write_var (s : prog_state) (var : var_name) (val : value) : option prog_state :=
  match var_lookup (ps_vars s) var with
  | Some (VarOwned a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocOwned) =>  (* Only allow if no active borrows *)
            let cell' := mk_cell val in
            let h' := heap_update (ps_heap s) a cell' LocOwned in
            Some (mk_prog_state h' (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
        | _ => None  (* Cannot write if borrowed *)
        end
      else None
  | Some (VarMutRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocMut _) =>
            let cell' := mk_cell val in
            let h' := heap_update (ps_heap s) a cell' (LocMut lt) in
            Some (mk_prog_state h' (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
        | _ => None
        end
      else None
  | Some (VarSharedRef _ _) => None  (* Cannot write through shared ref *)
  | None => None
  end.

(* Helper: remove a lifetime from a list *)
Fixpoint remove_lifetime (lts : list lifetime) (lt : lifetime) : list lifetime :=
  match lts with
  | [] => []
  | lt' :: rest => 
      if Nat.eqb (lt_id lt) (lt_id lt') then rest 
      else lt' :: remove_lifetime rest lt
  end.

(* Drop a variable (end its lifetime early) *)
Definition drop_var (s : prog_state) (var : var_name) : option prog_state :=
  match var_lookup (ps_vars s) var with
  | Some (VarOwned a lt) =>
      (* Check that no borrows outlive this lifetime *)
      if has_outliving_borrows (ps_heap s) a lt then
        None  (* Cannot drop - would leave dangling references *)
      else
        (* Remove variable from environment *)
        let vars' := var_remove (ps_vars s) var in
        Some (mk_prog_state (ps_heap s) vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
  | Some (VarSharedRef a lt) =>
      (* End shared borrow *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocShared lts) =>
          let lts' := remove_lifetime lts lt in
          let new_state := match lts' with
                          | [] => LocOwned
                          | _ => LocShared lts'
                          end in
          let h' := heap_update (ps_heap s) a cell new_state in
          let vars' := var_remove (ps_vars s) var in
          Some (mk_prog_state h' vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
      | _ => None
      end
  | Some (VarMutRef a lt) =>
      (* End mutable borrow *)
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocMut lt') =>
          if Nat.eqb (lt_id lt) (lt_id lt') then
            let h' := heap_update (ps_heap s) a cell LocOwned in
            let vars' := var_remove (ps_vars s) var in
            Some (mk_prog_state h' vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
          else None
      | _ => None
      end
  | None => None
  end.

(* Advance program state to next step *)
Definition step_forward (s : prog_state) : prog_state :=
  mk_prog_state (ps_heap s) (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) (S (ps_current_step s)).

(* Move operation: transfer ownership from one variable to another *)
Definition move_var (s : prog_state) (dest : var_name) (src : var_name) : option prog_state :=
  match var_lookup (ps_vars s) src with
  | Some (VarOwned a lt) =>
      if lifetime_active s lt then
        (* Check no active borrows before moving *)
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocOwned) =>
            (* Remove source variable and add destination with same ownership *)
            let vars' := var_remove (ps_vars s) src in
            let vars'' := var_update vars' dest (VarOwned a lt) in
            Some (mk_prog_state (ps_heap s) vars'' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
        | _ => None  (* Cannot move while borrowed *)
        end
      else None
  | _ => None  (* Can only move owned values *)
  end.

(* Copy operation: for Copy types, create a new owned value with same data *)
Definition copy_var (s : prog_state) (dest : var_name) (src : var_name) (lt_end : nat) 
    : option (prog_state * addr) :=
  match read_var s src with
  | Some val => let_owned s dest val lt_end
  | None => None
  end.
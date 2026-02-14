Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.

(** * Core Type Definitions *)

(** ** Basic Types *)
Definition var_name := string.
Definition addr := nat.
Definition lifetime_id := nat.

(** ** Lifetime Management *)
Record lifetime : Type := mk_lifetime {
  lt_id : lifetime_id;
  lt_start : nat;  (* When this lifetime begins (program counter / step) *)
  lt_end : nat     (* When this lifetime ends (must be explicitly set) *)
}.

(** ** Allocator Types *)
Record BitmapAllocator (S : PageSize) (n : Uint63.int) := mkBitmapAllocator {
  allocated : BitArray n;
  valid : BitArray n;
  range : PhysFrameRange S;
}.

Arguments mkBitmapAllocator {S} {n}.
Arguments allocated {S} {n}.
Arguments valid {S} {n}.
Arguments range {S} {n}.

(** ** Value Types *)
Inductive value : Type :=
  | VBool : bool -> value
  | VNat : nat -> value
  | VUnit : value
  | VPhysFrame : forall {S : PageSize}, PhysFrame S -> value
  | VPhysAddr : PhysAddr -> value
  | VUint63 : Uint63.int -> value
  | VBitArray : forall {n : Uint63.int}, BitArray n -> value
  | VPhysFrameRange : forall {S : PageSize}, PhysFrameRange S -> value
  | VAllocator : forall {S : PageSize} {n : Uint63.int}, BitmapAllocator S n -> value.

(** ** Ownership Model *)
Inductive var_ownership : Type :=
  | VarOwned : addr -> lifetime -> var_ownership        (* Immutable owned value *)
  | VarMutOwned : addr -> lifetime -> var_ownership     (* Mutable owned value *)
  | VarSharedRef : addr -> lifetime -> var_ownership    (* Shared reference *)
  | VarMutRef : addr -> lifetime -> var_ownership.      (* Mutable reference *)

Inductive location_state : Type :=
  | LocOwned : location_state                          (* No active borrows *)
  | LocShared : list lifetime -> location_state        (* Multiple shared borrows *)
  | LocMut : list lifetime -> location_state.          (* Stack of mutable borrows *)

Record mem_cell : Type := mk_cell {
  cell_value : value
}.

(** ** Program State *)
Definition heap := list (addr * mem_cell * location_state).
Definition var_env := list (var_name * var_ownership).

Record prog_state : Type := mk_prog_state {
  ps_heap : heap;
  ps_vars : var_env;
  ps_next_addr : addr;
  ps_next_lifetime_id : lifetime_id;
  ps_current_step : nat
}.

Definition empty_state : prog_state :=
  mk_prog_state [] [] 0 0 0.

(** * Lifetime Operations *)

Definition lifetime_outlives (lt1 lt2 : lifetime) : bool :=
  (Nat.leb (lt_start lt1) (lt_start lt2)) && 
  (Nat.leb (lt_end lt2) (lt_end lt1)).

Definition lifetime_contained_in (inner outer : lifetime) : bool :=
  (Nat.leb (lt_start outer) (lt_start inner)) && 
  (Nat.leb (lt_end inner) (lt_end outer)).

Definition lifetime_active (s : prog_state) (lt : lifetime) : bool :=
  (Nat.leb (lt_start lt) (ps_current_step s)) && 
  (Nat.ltb (ps_current_step s) (lt_end lt)).

Definition lifetime_eq (lt1 lt2 : lifetime) : bool :=
  Nat.eqb (lt_id lt1) (lt_id lt2).

Fixpoint remove_lifetime (lts : list lifetime) (lt : lifetime) : list lifetime :=
  match lts with
  | [] => []
  | lt' :: rest => 
      if Nat.eqb (lt_id lt) (lt_id lt') then rest 
      else lt' :: remove_lifetime rest lt
  end.

(** * Environment Operations *)

Fixpoint var_lookup (vars : var_env) (v : var_name) : option var_ownership :=
  match vars with
  | [] => None
  | (v', own) :: rest =>
      if String.eqb v v' then Some own else var_lookup rest v
  end.

Fixpoint var_update (vars : var_env) (v : var_name) (own : var_ownership) : var_env :=
  match vars with
  | [] => [(v, own)]
  | (v', own') :: rest =>
      if String.eqb v v' then (v, own) :: rest
      else (v', own') :: var_update rest v own
  end.

Definition var_remove (vars : var_env) (v : var_name) : var_env :=
  filter (fun '(v', _) => negb (String.eqb v v')) vars.

(** * Heap Operations *)

Fixpoint heap_lookup (h : heap) (a : addr) : option (mem_cell * location_state) :=
  match h with
  | [] => None
  | (a', cell, state) :: rest =>
      if Nat.eqb a a' then Some (cell, state) else heap_lookup rest a
  end.

Fixpoint heap_update (h : heap) (a : addr) (cell : mem_cell) (state : location_state) : heap :=
  match h with
  | [] => [(a, cell, state)]
  | (a', cell', state') :: rest =>
      if Nat.eqb a a' then (a, cell, state) :: rest
      else (a', cell', state') :: heap_update rest a cell state
  end.

Definition has_outliving_borrows (h : heap) (a : addr) (owner_lt : lifetime) : bool :=
  match heap_lookup h a with
  | Some (_, LocShared lts) => 
      existsb (fun lt => negb (lifetime_contained_in lt owner_lt)) lts
  | Some (_, LocMut lts) => 
      existsb (fun lt => negb (lifetime_contained_in lt owner_lt)) lts
  | _ => false
  end.

(** * Variable Creation Operations *)

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
  else None.

Definition let_mut_owned (s : prog_state) (var : var_name) (val : value) (lt_end : nat)
    : option (prog_state * addr) :=
  if Nat.ltb (ps_current_step s) lt_end then
    let a := ps_next_addr s in
    let lt_id := ps_next_lifetime_id s in
    let lt := mk_lifetime lt_id (ps_current_step s) lt_end in
    let cell := mk_cell val in
    let h' := heap_update (ps_heap s) a cell LocOwned in
    let vars' := var_update (ps_vars s) var (VarMutOwned a lt) in
    Some (mk_prog_state h' vars' (S a) (S lt_id) (ps_current_step s), a)
  else None.

(** * Borrowing Operations *)

Definition make_shared_borrow (s : prog_state) (ref_var : var_name) (a : addr) 
    (owner_lt : lifetime) (cell : mem_cell) (existing_state : location_state) 
    (borrow_end : nat) : option prog_state :=
  let lt_id := ps_next_lifetime_id s in
  let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
  if lifetime_contained_in borrow_lt owner_lt then
    let new_lts := match existing_state with
                   | LocOwned => [borrow_lt]
                   | LocShared lts => borrow_lt :: lts
                   | LocMut _ => [] (* Invalid case *)
                   end in
    let h' := heap_update (ps_heap s) a cell (LocShared new_lts) in
    let vars' := var_update (ps_vars s) ref_var (VarSharedRef a borrow_lt) in
    Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
  else None.

(** ** Shared Reference Creation *)
Definition let_shared_ref (s : prog_state) (ref_var : var_name) (owned_var : var_name) 
    (borrow_end : nat) : option prog_state :=
  match var_lookup (ps_vars s) owned_var with
  | Some (VarOwned a owner_lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, (LocOwned | LocShared _) as state) =>
          make_shared_borrow s ref_var a owner_lt cell state borrow_end
      | _ => None
      end
  | Some (VarMutOwned a owner_lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, (LocOwned | LocShared _) as state) =>
          make_shared_borrow s ref_var a owner_lt cell state borrow_end
      | _ => None
      end
  | Some (VarSharedRef a ref_lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocShared lts) =>
          make_shared_borrow s ref_var a ref_lt cell (LocShared lts) borrow_end
      | _ => None
      end
  | _ => None
  end.

(** ** Mutable Reference Creation *)
Definition let_mut_ref (s : prog_state) (ref_var : var_name) (owned_var : var_name) 
    (borrow_end : nat) : option prog_state :=
  match var_lookup (ps_vars s) owned_var with
  | Some (VarMutOwned a owner_lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocOwned) =>
          let lt_id := ps_next_lifetime_id s in
          let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
          if lifetime_contained_in borrow_lt owner_lt then
            let h' := heap_update (ps_heap s) a cell (LocMut [borrow_lt]) in
            let vars' := var_update (ps_vars s) ref_var (VarMutRef a borrow_lt) in
            Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
          else None
      | _ => None
      end
  | Some (VarMutRef a ref_lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocMut (loc_lt :: rest_stack)) =>
          if lifetime_eq loc_lt ref_lt then
            let lt_id := ps_next_lifetime_id s in
            let borrow_lt := mk_lifetime lt_id (ps_current_step s) borrow_end in
            if lifetime_contained_in borrow_lt ref_lt then
              let h' := heap_update (ps_heap s) a cell (LocMut (borrow_lt :: loc_lt :: rest_stack)) in
              let vars' := var_update (ps_vars s) ref_var (VarMutRef a borrow_lt) in
              Some (mk_prog_state h' vars' (ps_next_addr s) (S lt_id) (ps_current_step s))
            else None
          else None
      | _ => None
      end
  | _ => None
  end.

(** * Access Operations *)

(** ** Check if reading is allowed *)
Definition can_read (state : location_state) : bool :=
  match state with
  | LocOwned | LocShared _ => true
  | LocMut _ => false
  end.

(** ** Variable Reading *)
Definition read_var (s : prog_state) (var : var_name) : option value :=
  match var_lookup (ps_vars s) var with
  | Some (VarOwned a lt) | Some (VarMutOwned a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, state) =>
            if can_read state then Some (cell_value cell) else None
        | None => None
        end
      else None
  | Some (VarSharedRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocOwned) | Some (cell, LocShared _) => 
            Some (cell_value cell)
        | _ => None
        end
      else None
  | Some (VarMutRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (cell, LocMut (loc_lt :: _)) =>
            if lifetime_eq loc_lt lt then Some (cell_value cell) else None
        | _ => None
        end
      else None
  | None => None
  end.

(** ** Variable Writing *)
Definition write_var (s : prog_state) (var : var_name) (val : value) : option prog_state :=
  match var_lookup (ps_vars s) var with
  | Some (VarMutOwned a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (_, LocOwned) =>
            let cell' := mk_cell val in
            let h' := heap_update (ps_heap s) a cell' LocOwned in
            Some (mk_prog_state h' (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
        | _ => None
        end
      else None
  | Some (VarMutRef a lt) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (_, LocMut (loc_lt :: rest_stack)) =>
            if lifetime_eq loc_lt lt then
              let cell' := mk_cell val in
              let h' := heap_update (ps_heap s) a cell' (LocMut (loc_lt :: rest_stack)) in
              Some (mk_prog_state h' (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(** * Lifetime Management Operations *)

(** ** Variable Dropping *)
Definition drop_var (s : prog_state) (var : var_name) : option prog_state :=
  match var_lookup (ps_vars s) var with
  | Some (VarOwned a lt) | Some (VarMutOwned a lt) =>
      if has_outliving_borrows (ps_heap s) a lt then None
      else
        let vars' := var_remove (ps_vars s) var in
        Some (mk_prog_state (ps_heap s) vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
  | Some (VarSharedRef a lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocShared lts) =>
          let lts' := remove_lifetime lts lt in
          let new_state := if lts' then LocOwned else LocShared lts' in
          let h' := heap_update (ps_heap s) a cell new_state in
          let vars' := var_remove (ps_vars s) var in
          Some (mk_prog_state h' vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
      | _ => None
      end
  | Some (VarMutRef a lt) =>
      match heap_lookup (ps_heap s) a with
      | Some (cell, LocMut (loc_lt :: rest_stack)) =>
          if lifetime_eq loc_lt lt then
            let new_state := if rest_stack then LocOwned else LocMut rest_stack in
            let h' := heap_update (ps_heap s) a cell new_state in
            let vars' := var_remove (ps_vars s) var in
            Some (mk_prog_state h' vars' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
          else None
      | _ => None
      end
  | None => None
  end.

(** ** Step Forward *)
Definition step_forward (s : prog_state) : prog_state :=
  mk_prog_state (ps_heap s) (ps_vars s) (ps_next_addr s) (ps_next_lifetime_id s) 
                (S (ps_current_step s)).

(** * Transfer Operations *)

(** ** Move Semantics *)
Definition move_var (s : prog_state) (dest : var_name) (src : var_name) : option prog_state :=
  match var_lookup (ps_vars s) src with
  | Some ((VarOwned a lt) as own) | Some ((VarMutOwned a lt) as own) =>
      if lifetime_active s lt then
        match heap_lookup (ps_heap s) a with
        | Some (_, LocOwned) =>
            let vars' := var_remove (ps_vars s) src in
            let vars'' := var_update vars' dest own in
            Some (mk_prog_state (ps_heap s) vars'' (ps_next_addr s) (ps_next_lifetime_id s) (ps_current_step s))
        | _ => None
        end
      else None
  | _ => None
  end.

(** ** Copy Semantics *)
Definition copy_var (s : prog_state) (dest : var_name) (src : var_name) (lt_end : nat) 
    : option (prog_state * addr) :=
  match read_var s src with
  | Some val => let_owned s dest val lt_end
  | None => None
  end.

Definition copy_var_mut (s : prog_state) (dest : var_name) (src : var_name) (lt_end : nat) 
    : option (prog_state * addr) :=
  match read_var s src with
  | Some val => let_mut_owned s dest val lt_end
  | None => None
  end.
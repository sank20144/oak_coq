Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.

(* Memory addresses *)
Definition addr := nat.

(* Values stored in memory  *)
Inductive value : Type :=
  | VBool : bool -> value
  | VNat : nat -> value
  | VUnit : value
  
  | VPhysFrame : forall {S : PageSize}, PhysFrame S -> value
  | VPhysAddr : PhysAddr -> value
  | VUint63 : Uint63.int -> value
  | VBitArray : forall {n : nat}, BitArray n -> value
  | VPhysFrameRange : forall {S : PageSize}, PhysFrameRange S -> value
  | VAllocator : forall {S : PageSize} {n : nat}, 
      BitArray n -> BitArray n -> PhysFrameRange S -> value. (* allocated, valid, range *)

(* Memory cell containing value *)
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
  (mk_memory h' (S a), a).

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

Definition read_frame {S : PageSize} (p : program_state) (a : addr) : option (PhysFrame S) :=
  match read p a with
  | Some (@VPhysFrame S0 frame) => 
      match PageSize_eq_dec S0 S with
      | left H => Some (eq_rect S0 (fun s => PhysFrame s) frame S H)
      | right _ => None
      end
  | _ => None
  end.

Definition write_frame {S : PageSize} (p : program_state) (a : addr) (frame : PhysFrame S) : option program_state :=
  write p a (VPhysFrame frame).

Definition read_phys_addr (p : program_state) (a : addr) : option PhysAddr :=
  match read p a with
  | Some (VPhysAddr paddr) => Some paddr
  | _ => None
  end.

Definition read_bool (p : program_state) (a : addr) : option bool :=
  match read p a with
  | Some (VBool b) => Some b
  | _ => None
  end.

Definition read_nat (p : program_state) (a : addr) : option nat :=
  match read p a with
  | Some (VNat n) => Some n
  | _ => None
  end.

Definition read_uint63 (p : program_state) (a : addr) : option Uint63.int :=
  match read p a with
  | Some (VUint63 u) => Some u
  | _ => None
  end.

Definition write_uint63 (p : program_state) (a : addr) (u : Uint63.int) : option program_state :=
  write p a (VUint63 u).

Definition read_bitarray {n : nat} (p : program_state) (a : addr) : option (BitArray n) :=
  match read p a with
  | Some (@VBitArray n0 arr) => 
      match Nat.eq_dec n n0 with
      | left H => eq_rect n0 (fun m => option (BitArray m)) (Some arr) n (eq_sym H)
      | right _ => None
      end
  | _ => None
  end.

Definition write_bitarray {n : nat} (p : program_state) (a : addr) (arr : BitArray n) : option program_state :=
  write p a (VBitArray arr).

Definition read_frame_range {S : PageSize} (p : program_state) (a : addr) : option (PhysFrameRange S) :=
  match read p a with
  | Some (@VPhysFrameRange S0 range) => 
      match PageSize_eq_dec S0 S with
      | left H => Some (eq_rect S0 (fun s => PhysFrameRange s) range S H)
      | right _ => None
      end
  | _ => None
  end.

Definition write_frame_range {S : PageSize} (p : program_state) (a : addr) (range : PhysFrameRange S) : option program_state :=
  write p a (VPhysFrameRange range).

Definition read_allocator {S : PageSize} {n : nat} (p : program_state) (a : addr) : 
  option (BitArray n * BitArray n * PhysFrameRange S) :=
  match read p a with
  | Some (@VAllocator S' n' allocated valid range) =>
      match Nat.eq_dec n' n with
      | left Hn =>
          match PageSize_eq_dec S' S with
          | left Hs =>
              let allocated' := eq_rect n' (fun m => BitArray m) allocated n Hn in
              let valid' := eq_rect n' (fun m => BitArray m) valid n Hn in
              let range' := eq_rect S' (fun s => PhysFrameRange s) range S Hs in
              Some (allocated', valid', range')
          | right _ => None
          end
      | right _ => None
      end
  | _ => None
  end.

Definition write_allocator {S : PageSize} {n : nat} (p : program_state) (a : addr) 
  (allocated valid : BitArray n) (range : PhysFrameRange S) : option program_state :=
  write p a (VAllocator allocated valid range).

(* Update only the allocated bitmap of an allocator *)
Definition update_allocator_allocated {S : PageSize} {n : nat} (p : program_state) (a : addr)
  (new_allocated : BitArray n) : option program_state :=
  match read_allocator p a with
  | Some (_, valid, range) => @write_allocator S n p a new_allocated valid range
  | None => None
  end.

(* Update only the valid bitmap of an allocator *)
Definition update_allocator_valid {S : PageSize} {n : nat} (p : program_state) (a : addr)
  (new_valid : BitArray n) : option program_state :=
  match read_allocator p a with
  | Some (allocated, _, range) => @write_allocator S n p a allocated new_valid range
  | None => None
  end.
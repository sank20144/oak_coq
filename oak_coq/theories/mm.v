From stdpp Require Import base list.
(* Strictly only dealing with 2MB pages here *)

(* These should only be 2^64 *)
(* If we make these a bitarray of size 64, we can embed the flags inside the pte_paddr itself *)
Definition p_addr := nat.

Record v_addr := {
  pml4_idx : nat ;
  pdp_idx : nat ;
  pd_idx : nat ;
  pt_idx : nat ;
  offset : nat ;
}.

Inductive Syscall :=
| sc_mmap.

Definition BitArray (size: nat) := list bool. (* I think this is the correct struct for this *)

Record PhysFrameRange := {
  pfr_start : p_addr ;
  pfr_end : p_addr ;
}.

(* Used to keep track of the physical memory frames *)
Record BitMapAllocator := {
(* 4096 was what was used in the kernel for size which is tracking 512 gigs of memory ((4096 * 64)Frames * 2MB). So this should realistically be 262,144 (4096 * 64) since we use a bool list*) 
  allocated : BitArray 4096; 
  valid : BitArray 4096;
  range : PhysFrameRange ; 
}.

Inductive PageTableFlag := 
  | Present
  | Writable 
  | UserAccessible
  | WriteThrough
  | NoCache
  | Accessed
  | Dirty
  | HugePage
  | Global
  | Encrypted
  | NoExecute.

(* These are syscall level flags that get translated to hardware level Page Table flags during the MMAP syscall *)
Inductive MmapProtectionFlags :=
  | PROT_READ
  | PROT_WRITE
  | PROT_EXEC
  | PROT_NONE.

Inductive MmapFlags :=
  | MAP_PRIVATE
  | MAP_FIXED
  | MAP_ANONYMOUS.

(* *************** *)


(* Frame allocation related things *)

(* Find first set bit in a list of booleans *)
Fixpoint first_one (bits: list bool) : option nat :=
  match bits with
  | [] => None
  | true :: _ => Some 0
  | false :: rest => 
      match first_one rest with
      | None => None
      | Some n => Some (S n)
      end
  end.

Compute (first_one [false; false; false; false; false; true]).

(* Bitwise AND of two boolean lists *)
Fixpoint bitand (l1 l2: list bool) : list bool :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (andb x y) :: (bitand xs ys)
  end.

Compute (bitand [true; false; true] [true; true; false]).

(* Bitwise NOT of a boolean list *)
Fixpoint bitnot (l: list bool) : list bool :=
  match l with
  | [] => []
  | x::xs => (negb x) :: (bitnot xs)
  end.

Compute (bitnot [true; false; true]).

(* Set bit at index *)
Fixpoint set_bit (bits: list bool) (idx: nat) (val: bool) : list bool :=
  match bits, idx with
  | [], _ => []
  | b::bs, 0 => val::bs
  | b::bs, S n => b::(set_bit bs n val)
  end.

Compute (set_bit [true; false; true] 1 true).

(* Frame allocation function *)
Definition allocate_frame (bm: BitMapAllocator) : option (BitMapAllocator * p_addr) :=
  match first_one (bitand (bm.(valid)) (bitnot bm.(allocated))) with
  | None => None
  | Some idx => 
      let new_allocated := set_bit bm.(allocated) idx true in
      let new_bm := {| 
        allocated := new_allocated;
        valid := bm.(valid);
        range := bm.(range)
      |} in
      Some (new_bm, bm.(range).(pfr_start) + idx)
  end.

Compute (allocate_frame {| allocated := [true; false; true]; valid := [true; true; true]; range := {| pfr_start := 0; pfr_end := 2 |} |}).

(* Page table related things *)

Inductive PTLevel :=
  | PML4_LEVEL  (* Level 4 *)
  | PDP_LEVEL   (* Level 3 *)
  | PD_LEVEL    (* Level 2 *)
  | PT_LEVEL.   (* Level 1 *)

(* Page table entry *)
Record PTE := {
  pte_paddr : p_addr ;
  pte_flags : list PageTableFlag ; (* In reality, flags are embedded inside the p_addr itself*)
}.

(* Page table *)
Record PageTable := {
  pt_entries : list PTE ; (* Should be only 512 *)
  level : PTLevel (* 4 = PML4, 3 = PDP, 2 = PD, 1 = PT *)
}.

Definition get_pt_index (addr: v_addr) (level: PTLevel) : nat :=
  match level with
  | PML4_LEVEL => addr.(pml4_idx)
  | PDP_LEVEL => addr.(pdp_idx)
  | PD_LEVEL => addr.(pd_idx)
  | PT_LEVEL => addr.(pt_idx)
  end.


(* TODO: Page table walk *)

(**********)

(* Process related things *)

Record Process := {
  p_pml4 : {pt : PageTable | pt.(level) = PML4_LEVEL} ;
  p_pid : nat ;
  p_ksp : v_addr ; (* Kernel stack pointer *)
  p_usp : v_addr ; (* User stack pointer *)
}.

(*************)

(* Main syscall related things *)

(* Base flags *)
Definition base_pt_flags := [Present; UserAccessible; Encrypted].

(* Main protection flags to page table flags conversion *)
Definition prot_to_ptflags (prot: list MmapProtectionFlags) : list PageTableFlag :=
  match prot with
  | [] => base_pt_flags ++ [NoExecute]
  | [PROT_READ] => base_pt_flags ++ [NoExecute]
  | [PROT_WRITE] => base_pt_flags ++ [Writable; NoExecute]
  | [PROT_EXEC] => base_pt_flags
  | [PROT_WRITE; PROT_EXEC] => base_pt_flags ++ [Writable]
  | [PROT_EXEC; PROT_WRITE] => base_pt_flags ++ [Writable]
  | _ => base_pt_flags ++ [NoExecute] 
  end.

(* Gets the needed address, size, protflags and memflags from user process 
-> Checks if the needed address is fixed -> Converts syscall flags to hardware flags
-> Finds and allocate pages in the users page tables and finds frames to back them up
-> Maps them -> flush tlb -> return pointer to virtual memory start *)

Definition Mmap := nat.
 (* TODO *)
  

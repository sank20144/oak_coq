From stdpp Require Import base list.

(* Strictly only dealing with 2MB pages here *)

(* These should only be 2^64 *)
(* If we make these a bitarray of size 64, we can embed the flags inside the pte_paddr itself *)
Definition p_addr := nat.
Definition v_addr := nat.

(* Inductive Syscall :=
| sc_mmap.

Definition BitArray (size: nat) := list bool. I think this is the correct struct for this *)

Record PhysFrame := {
  pf_addr : p_addr ;
}.

Record PhysFrameRange := {
  pfr_start : PhysFrame ;
  pfr_end : PhysFrame ;
}.

Record Process := {
  p_pml4 : PhysFrame ;
  p_pid : nat ;
  p_ksp : v_addr ; (* Kernel stack pointer *)
  p_usp : v_addr ; (* User stack pointer  *)
}.

(* Basically a refined bitmap allocator *)
Record MemoryState := {
  valid_frames : list PhysFrame;
  allocated_frames : list PhysFrame;
  frame_owners : list (PhysFrame * Process)
}.
(* Frame equality check *)
Definition frame_eq (f1 f2: PhysFrame) : bool :=
  Nat.eqb f1.(pf_addr) f2.(pf_addr).

(* Process equality check (based on PID) *)
Definition proc_eq (p1 p2: Process) : bool :=
  Nat.eqb p1.(p_pid) p2.(p_pid).

(* Check if a frame is in a list of frames *)
Fixpoint frame_in_list (frame: PhysFrame) (frames: list PhysFrame) : bool :=
  match frames with
  | [] => false
  | curr :: rest => 
      if frame_eq frame curr 
      then true
      else frame_in_list frame rest
  end.

(* Find owner of a frame *)
Fixpoint get_frame_owner (frame: PhysFrame) (owners: list (PhysFrame * Process)) : option Process :=
  match owners with
  | [] => None
  | (curr_frame, curr_proc) :: rest => 
      if frame_eq frame curr_frame
      then Some curr_proc
      else get_frame_owner frame rest
  end.
(* Add or update a frame owner in the list *)
Fixpoint set_frame_owner (frame: PhysFrame) (proc: Process) 
                        (owners: list (PhysFrame * Process)) 
                        : list (PhysFrame * Process) :=
  match owners with
  | [] => [(frame, proc)]  
  | (curr_frame, curr_proc) :: rest =>
      if frame_eq frame curr_frame
      then (frame, proc) :: set_frame_owner frame proc rest  
      else (curr_frame, curr_proc) :: set_frame_owner frame proc rest  
  end.

(* Remove a frame from a list *)
Fixpoint remove_frame (frame: PhysFrame) (frames: list PhysFrame) : list PhysFrame :=
  match frames with
  | [] => [] 
  | curr :: rest => 
      if frame_eq frame curr
      then remove_frame frame rest 
      else curr :: remove_frame frame rest  
  end.

(* Remove ownership of a frame *)
Fixpoint remove_frame_owner (frame: PhysFrame) (owners: list (PhysFrame * Process)) 
                           : list (PhysFrame * Process) :=
  match owners with
  | [] => [] 
  | (curr_frame, curr_proc) :: rest =>
      if frame_eq frame curr_frame 
      then remove_frame_owner frame rest  
      else (curr_frame, curr_proc) :: remove_frame_owner frame rest  
  end.

(* Allocation operation *)
Definition alloc (state: MemoryState) (proc: Process) (frame: PhysFrame) : option MemoryState :=
  if andb (frame_in_list frame state.(valid_frames))
          (negb (frame_in_list frame state.(allocated_frames)))
  then 
    Some {|
      valid_frames := state.(valid_frames);
      allocated_frames := frame :: state.(allocated_frames);
      frame_owners := set_frame_owner frame proc state.(frame_owners)
    |}
  else None.

(* For 2 different processes, when allocating a frame for a memory state 
'state' should return Some new state 'state1' and allocating the same frame for
another process in new state 'state1' should return None *)
Theorem no_double_allocation: forall state state1 p1 p2 frame,
  p1.(p_pid) <> p2.(p_pid) ->
  alloc state p1 frame = Some state1 ->
  alloc state1 p2 frame = None.
Proof.
  Admitted.


(* Deallocating frame - not considering range *)
Definition dealloc (state: MemoryState) (frame: PhysFrame) : option MemoryState :=
  if andb (frame_in_list frame state.(valid_frames))
          (frame_in_list frame state.(allocated_frames))
  then 
    Some {|
      valid_frames := state.(valid_frames);
      allocated_frames := remove_frame frame state.(allocated_frames);
      frame_owners := remove_frame_owner frame state.(frame_owners)
    |}
  else None.




(* Process related things *)

(* This is the struct that will be used to keep track of the physical memory frames *)

(* Used to keep track of the physical memory frames *)
(* Record BitMapAllocator := {
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

Compute (allocate_frame {| allocated := [false; false; true]; valid := [true; true; true]; range := {| pfr_start := 0; pfr_end := 0 |} |}).

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

(* Definition get_pt_index (addr: v_addr) (level: PTLevel) : nat :=
  match level with
  | PML4_LEVEL => addr.(pml4_idx)
  | PDP_LEVEL => addr.(pdp_idx)
  | PD_LEVEL => addr.(pd_idx)
  | PT_LEVEL => addr.(pt_idx)
  end. *)


(* TODO: Page table walk *)

(**********)



(*************)

(* Main syscall related things *)

(* Base flags *)
Definition base_pt_flags : list PageTableFlag := [Present; UserAccessible; Encrypted].

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

Definition Mmap := nat. *)
 (* TODO *)
  
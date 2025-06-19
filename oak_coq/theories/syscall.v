Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Lia.
Import ListNotations.

From XY Require Export mm2.

(** * Process and System Types *)

(** Process identifier *)
Definition ProcessId := nat.

(** Virtual address representation *)
Definition VirtAddr := Z.

(** * mmap Protection and Flags *)

(** mmap Protection flags *)
Inductive MmapProtection : Type :=
  | PROT_READ
  | PROT_WRITE
  | PROT_EXEC.

Definition MmapProtectionSet := list MmapProtection.

Definition mmap_prot_eq (f1 f2 : MmapProtection) : bool :=
  match f1, f2 with
  | PROT_READ, PROT_READ => true
  | PROT_WRITE, PROT_WRITE => true
  | PROT_EXEC, PROT_EXEC => true
  | _, _ => false
  end.

(** Check if a protection set contains a specific protection *)
Definition prot_contains (prots: MmapProtectionSet) (p: MmapProtection) : bool :=
  existsb (fun x => mmap_prot_eq x p ) prots.

(** Check if a protection set contains a specific protection *)

(** mmap Flags *)
Inductive MmapFlag : Type :=
  | MAP_PRIVATE
  | MAP_FIXED
  | MAP_ANONYMOUS.

Definition MmapFlagSet := list MmapFlag.

Definition mmap_flag_eq (f1 f2 : MmapFlag) : bool :=
  match f1, f2 with
  | MAP_PRIVATE, MAP_PRIVATE => true
  | MAP_FIXED, MAP_FIXED => true
  | MAP_ANONYMOUS, MAP_ANONYMOUS => true
  | _, _ => false
  end.

(** Check if a flag set contains a specific flag *)
Definition flag_contains (flags: MmapFlagSet) (f: MmapFlag) : bool :=
  existsb (fun x => mmap_flag_eq x f) flags.

(** * Error Representation *)

(** Error types for mmap operations *)
Inductive Errno : Type :=
  | EIO    (* Input/output error *)
  | EBADF    (* Bad file descriptor *)
  | ENOMEM    (* Not enough memory *)
  | EFAULT    (* Bad address *)
  | EINVAL (* Invalid argument *)
  | ENOSYS. (* Function not implemented *)

(** * Page Tables and Memory Representation *)

(** Page table flags *)
Inductive PageTableFlag : Type :=
  | PF_PRESENT
  | PF_WRITABLE
  | PF_USER_ACCESSIBLE
  | PF_NO_EXECUTE
  | PF_ENCRYPTED.

Definition PageTableFlagSet := list PageTableFlag.

Definition ptflag_eq (f1 f2 : PageTableFlag) : bool :=
  match f1, f2 with
  | PF_PRESENT, PF_PRESENT => true
  | PF_WRITABLE, PF_WRITABLE => true
  | PF_USER_ACCESSIBLE, PF_USER_ACCESSIBLE => true
  | PF_NO_EXECUTE, PF_NO_EXECUTE => true
  | PF_ENCRYPTED, PF_ENCRYPTED => true
  | _, _ => false
  end.

(** Check if a flag set contains a specific flag *)
Definition ptflag_contains (flags: PageTableFlagSet) (f: PageTableFlag) : bool :=
  existsb (fun x => ptflag_eq x f) flags.

(** A mapping entry in a page table *)
Record PageTableEntry := mkPageTableEntry {
  pte_virt_addr : VirtAddr;
  pte_phys_addr : PhysAddr;
  pte_page_size : PageSize;
  pte_flags : PageTableFlagSet
}.

(** The page table for a process *)
Definition PageTable := list PageTableEntry.

Module VirtAddrMap := FMapAVL.Make(Z_as_OT).

(** A memory mapping in a process's address space *)
Record MemoryMapping := mkMemoryMapping {
  mm_start_addr : VirtAddr;
  mm_size : Z;
}.

(** A process with its page table and memory mappings *)
Record Process := mkProcess {
  proc_id : ProcessId;
  proc_page_table : PageTable;
  proc_memory_mappings : VirtAddrMap.t MemoryMapping;
}.

Axiom proc_id_injective : forall p1 p2,
  proc_id p1 = proc_id p2 -> p1 = p2.

(** The system state with all processes and the frame allocator *)
Record SystemState (S : PageSize) := mkSystemState {
  processes : list Process;
  frame_allocator : BitmapAllocator S;
  
  (* System invariant: process IDs must be unique *)
  sys_unique_pids : forall p1 p2,
    In p1 processes -> In p2 processes -> 
    proc_id p1 = proc_id p2 -> p1 = p2;
  
}.

(** Convert MmapProtection to PageTableFlags *)
Definition prot_to_ptflags (prots: MmapProtectionSet) : PageTableFlagSet :=
  PF_PRESENT :: PF_USER_ACCESSIBLE :: PF_ENCRYPTED ::
  (if prot_contains prots PROT_EXEC then [] else [PF_NO_EXECUTE]) ++
  (if prot_contains prots PROT_WRITE then [PF_WRITABLE] else []).

(** Check if a virtual address range is unallocated in a page table *)
Definition is_range_unallocated (pt: PageTable) (start: VirtAddr) (mapping_size: Z) : bool :=
  forallb (fun pte => 
    let pte_end := (pte_virt_addr pte + size (pte_page_size pte))%Z in
    let request_end := (start + mapping_size)%Z in
    (pte_end <=? start)%Z || (request_end <=? pte_virt_addr pte)%Z
  ) pt.

(** Find a process by ID *)
Definition find_process {S : PageSize} (sys: SystemState S) (pid: ProcessId) : option Process :=
  find (fun p => if proc_id p =? pid then true else false) (processes S sys).

(** Check if a page size is supported *)
Definition is_supported_page_size (ps: PageSize) : bool :=
  let sz := size ps in
  ((Z.eqb sz 4096) || (Z.eqb sz 2097152) || (Z.eqb sz 1073741824)).

(* Create a 2MiB page size constant *)
Program Definition PAGE_SIZE_2MB : PageSize := 
  {| size := 2097152; size_positive := _ |}.
Next Obligation.
simpl. lia.
Qed.

(** Align an address to a page size boundary *)
Definition align_up (addr: Z) (ps: PageSize) : Z :=
  let mask := Z.sub (size ps) 1 in
  Z.mul (Z.div (Z.add addr mask) (size ps)) (size ps).

Compute align_up 2097151%Z PAGE_SIZE_2MB.

(** Create a range of page table entries *)
Fixpoint create_pte_range_nat
  (vaddr: VirtAddr) (paddr: PhysAddr) (count: nat) (ps: PageSize) (flags: PageTableFlagSet)
  : list PageTableEntry :=
  match count with
  | O => []
  | S n => 
    let pte := {|
      pte_virt_addr := vaddr;
      pte_phys_addr := paddr;
      pte_page_size := ps;
      pte_flags := flags
    |} in
    let sz := size ps in
    pte :: create_pte_range_nat (vaddr + sz)%Z (paddr + sz)%Z n ps flags
  end.

Definition create_pte_range
  (vaddr: VirtAddr) (paddr: PhysAddr) (remaining: Z) (ps: PageSize) (flags: PageTableFlagSet)
  : list PageTableEntry :=
  if Z.leb remaining 0 then []
  else
    let sz := size ps in
    let count := Z.to_nat (Z.div (remaining + sz - 1) sz) in (* Ceiling division *)
    create_pte_range_nat vaddr paddr count ps flags.


Fixpoint alloc_frames_nat {S: PageSize}(alloc: BitmapAllocator S) (n: nat) (acc: list (PhysFrame S)) : 
          list (PhysFrame S) * BitmapAllocator S + Errno :=
        match n with
        | O => inl (acc, alloc)
        | S n' =>
          match allocate_frame alloc with
          | Some (frame, new_alloc) => alloc_frames_nat new_alloc n' (frame :: acc)
          | None => inr ENOMEM
          end
        end.

(* Definition allocate_frames (alloc: BitmapAllocator size_4k) (n: nat) : 
          list (PhysFrame size_4k) * BitmapAllocator size_4k + Errno :=
  alloc_frames_nat alloc n [].


Compute 
  let alloc := marked_allocator_0_128k in
  match allocate_frames alloc 2 with
  | inl (frames, new_alloc) => 
      (map (fun f => start_address _ f) frames,
       valid _ new_alloc, 
       allocated _ new_alloc)
  | inr _ => ([], [], [])
  end. *)

(* Function to check if an address is aligned to page size *)
Definition is_aligned (addr : VirtAddr) (ps : PageSize) : bool :=
  Z.eqb (Z.modulo addr (size ps)) 0.

(* Representation of a slice of bytes (return type of mmap) *)
Record ByteSlice := mkByteSlice {
  slice_addr : VirtAddr;
  slice_size : Z;
}.

(* Result type for mmap operation *)
Inductive MmapResult :=
  | MmapSuccess (slice : ByteSlice)
  | MmapError (error : Errno).

(* Helper to allocate frames from the BitmapAllocator *)
Fixpoint allocate_frames {S : PageSize} (count : nat) (alloc : BitmapAllocator S) 
                        : option (list (PhysFrame S) * BitmapAllocator S) :=
  match count with
  | O => Some ([], alloc)
  | S n =>
    match allocate_frame alloc with
    | Some (frame, new_alloc) =>
      match allocate_frames n new_alloc with
      | Some (frames, final_alloc) => Some (frame :: frames, final_alloc)
      | None => None
      end
    | None => None
    end
  end.

(* Function to replace a process in a list of processes *)
Fixpoint replace_process (old_proc : Process) (new_proc : Process) (procs : list Process) : list Process :=
  match procs with
  | [] => []
  | p :: ps =>
    if proc_id p =? proc_id old_proc
    then new_proc :: ps
    else p :: replace_process old_proc new_proc ps
  end.

(* Function to add a memory mapping to a process *)
Definition add_mapping (proc : Process) (addr : VirtAddr) (mapping : MemoryMapping) : Process :=
  {|
    proc_id := proc_id proc;
    proc_page_table := proc_page_table proc;
    proc_memory_mappings := VirtAddrMap.add addr mapping (proc_memory_mappings proc);
  |}.

(* Function to add page table entries to a process *)
Definition add_ptes (proc : Process) (ptes : list PageTableEntry) : Process :=
  {|
    proc_id := proc_id proc;
    proc_page_table := proc_page_table proc ++ ptes;
    proc_memory_mappings := proc_memory_mappings proc;
  |}.

(* The mmap syscall implementation *)
Program Definition mmap (sys : SystemState PAGE_SIZE_2MB) (pid : ProcessId) 
                (addr_opt : option VirtAddr) (sz : Z) 
                (prot : MmapProtectionSet) (flags : MmapFlagSet) 
                : (MmapResult * SystemState PAGE_SIZE_2MB ) :=
  
  (* Check if size is valid *)
  if Z.leb sz 0 then
    (MmapError EINVAL, sys)
  
  (* Check if required flags are present *)
  else if negb (flag_contains flags MAP_ANONYMOUS) || negb (flag_contains flags MAP_PRIVATE) then
    (MmapError EINVAL, sys)
    
  (* Find the process *)
  else
    match find_process sys pid with
    | None => (MmapError EINVAL, sys)
    | Some proc =>
      
      (* Determine starting address based on flags *)
      let addr_result :=
        if flag_contains flags MAP_FIXED then
          (* For MAP_FIXED, use the exact address *)
          match addr_opt with
          | None => inr EINVAL
          | Some a =>
            if is_aligned a PAGE_SIZE_2MB && (Z.geb a (size PAGE_SIZE_2MB)) then
              inl a
            else
              inr EINVAL
          end
        else
          (* For non-MAP_FIXED, we can adjust the address *)
          let base_addr :=
            match addr_opt with
            | None => size PAGE_SIZE_2MB
            | Some a => Z.max a (size PAGE_SIZE_2MB)
            end in
          inl (align_up base_addr PAGE_SIZE_2MB)
      in
      
      match addr_result with
      | inr err => (MmapError err, sys)
      | inl start_addr =>
        
        (* Round up size to page boundary *)
        let aligned_size := align_up sz PAGE_SIZE_2MB in
        
        (* Check if address range is free *)
        if negb (is_range_unallocated (proc_page_table proc) start_addr aligned_size) then
          (MmapError ENOMEM, sys)
        else
          
          (* Calculate number of pages needed *)
          let frame_count := Z.to_nat (Z.div aligned_size (size PAGE_SIZE_2MB)) in
          
          (* Allocate physical frames *)
          match allocate_frames frame_count (frame_allocator PAGE_SIZE_2MB sys) with
          | None => (MmapError ENOMEM, sys)
          | Some (frames, allocator) =>
            
            (* Convert protection flags to page table flags *)
            let pt_flags := prot_to_ptflags prot in
            
            (* Create page table entries *)
            let ptes := 
              match frames with
              | [] => [] (* Should never happen if frame_count > 0 *)
              | first_frame :: _ =>
                create_pte_range 
                  start_addr 
                  (start_address PAGE_SIZE_2MB first_frame) 
                  aligned_size 
                  PAGE_SIZE_2MB 
                  pt_flags
              end in
            
            (* Create memory mapping record *)
            let mapping := {|
              mm_start_addr := start_addr;
              mm_size := aligned_size;
            |} in
            
            (* Update process with new page table entries and mapping *)
            let new_proc := add_ptes (add_mapping proc start_addr mapping) ptes in
            
            (* Update system state *)
            let new_processes := replace_process proc new_proc (processes PAGE_SIZE_2MB sys) in
            
            (* Create new system state *)
            let new_sys := {|
              processes := new_processes;
              frame_allocator := allocator;
              sys_unique_pids := _;
            |} in
            
            (* Return success with the mapped memory slice *)
            let result := MmapSuccess (mkByteSlice start_addr aligned_size) in
            (result, new_sys)
          end
      end
    end.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Definition frame_0 : PhysFrame size_4k. 
Proof. refine {|
  start_address := 0%Z;
  frame_aligned := _ 
|}.
  simpl. reflexivity.
Defined.

Definition frame_8k : PhysFrame size_4k. 
Proof. refine {|
  start_address := 8192%Z;
  frame_aligned := _
|}.
  simpl. reflexivity.
Defined.


(* Create an empty system state *)
Program Definition empty_system_state (S : PageSize) (r : PhysFrameRange S) : SystemState S := 
  {|
    processes := [];
    frame_allocator := new_allocator r;
    sys_unique_pids := _;
  |}.
Next Obligation.
  contradiction.
Qed.

Program Definition one_process_system_state (S : PageSize) (r : PhysFrameRange S) (pid : ProcessId) : SystemState S := 
  {|
    processes := [{| proc_id := pid; proc_page_table := []; proc_memory_mappings := VirtAddrMap.empty MemoryMapping |}];
    frame_allocator := new_allocator r;
    sys_unique_pids := _;
  |}.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Program Definition marked_process_system_state (S : PageSize) (r : PhysFrameRange S) (pid : ProcessId) : SystemState S :=
  match mark_valid (new_allocator r) r true with
  | Some marked_alloc =>
    {|
      processes := [{| proc_id := pid; proc_page_table := []; 
                       proc_memory_mappings := VirtAddrMap.empty MemoryMapping |}];
      frame_allocator := marked_alloc;
      sys_unique_pids := _;
    |}
  | None => one_process_system_state S r pid
  end.
Next Obligation.
  apply proc_id_injective.
  assumption.
Qed.

Definition range_0_64m : PhysFrameRange PAGE_SIZE_2MB.
Proof.
  refine {|
    start_frame := {| start_address := 0%Z; frame_aligned := _ |};
    end_frame := {| start_address := 67108864%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.

Definition range_128mb_512mb : PhysFrameRange PAGE_SIZE_2MB.
Proof.
  refine {|
    start_frame := {| start_address := 134217728%Z; frame_aligned := _ |};
    end_frame := {| start_address := 536870912%Z; frame_aligned := _ |};
    range_valid := _
  |}.
  - simpl. lia. Unshelve. simpl. reflexivity. simpl. reflexivity.
  Defined.


(* Test cases for mmap function *)

(* Not allowed to map since no process with pid 1 *)
Compute (mmap (empty_system_state PAGE_SIZE_2MB range_0_64m) 1 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Not enough memory since bitmapallocator not initialized *)
Compute (mmap (one_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Mapping a single page *)
Compute (mmap (marked_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 
         (Some 4096%Z) 8192%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Page table after mapping a single page *)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_0_64m 0) 0 
         (Some 4096666%Z) 819254%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | (MmapSuccess _, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | _ => []
         end.

(* Mapping a range of pages *)
Compute (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]).

(* Page table after mapping a range of pages *)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | ( MmapSuccess _, new_sys) => 
             let proc := find (fun p => Nat.eqb (proc_id p) 0) (processes _ new_sys) in
             match proc with
             | Some p => proc_page_table p
             | None => []
             end
         | _ => []
         end.

(* *)

(* Returned starting virtual address*)
Compute match (mmap (marked_process_system_state PAGE_SIZE_2MB range_128mb_512mb 0) 0 
         (Some 4096%Z) 8192000%Z [PROT_READ] [MAP_PRIVATE; MAP_ANONYMOUS]) with
         | ( MmapSuccess bs, new_sys) => 
             bs 
         | _ => mkByteSlice 0%Z 0%Z
         end.

Compute align_up 8192000%Z PAGE_SIZE_2MB.

(** No overlapping allocations *)
Theorem mmap_no_overlap : forall (sys: SystemState PAGE_SIZE_2MB) pid1 pid2 addr1 addr2 size1 size2 prot1 prot2 flags1 flags2 vaddr1 vaddr2 new_sys1 new_sys2,
  mmap sys pid1 addr1 size1 prot1 flags1 = (MmapSuccess (mkByteSlice vaddr1 size1), new_sys1)  ->
  mmap new_sys1 pid2 addr2 size2 prot2 flags2 = (MmapSuccess (mkByteSlice vaddr2 size2), new_sys2) ->
  (pid1 <> pid2 \/ 
   Z.le (Z.add vaddr1 (align_up size1 PAGE_SIZE_2MB)) vaddr2 \/ 
   Z.le (Z.add vaddr2 (align_up size2 PAGE_SIZE_2MB)) vaddr1).

(** Physical frames are properly accounted for in the allocator *)
Theorem mmap_frames_allocated : forall (sys: SystemState PAGE_SIZE_2MB) pid addr sz prot flags vaddr new_sys,
  mmap sys pid addr sz prot flags = (MmapSuccess (mkByteSlice vaddr sz), new_sys) ->
  count_ones (allocated PAGE_SIZE_2MB (frame_allocator PAGE_SIZE_2MB new_sys)) = 
  count_ones (allocated PAGE_SIZE_2MB (frame_allocator PAGE_SIZE_2MB sys)) + 
  Z.to_nat ((align_up sz PAGE_SIZE_2MB) / (size PAGE_SIZE_2MB)).

(** MAP_FIXED respects the provided address *)
Theorem mmap_fixed_respects_addr : forall {S: PageSize} (sys: SystemState S) pid addr size prot flags vaddr new_sys,
  flag_contains flags MAP_FIXED = true ->
  mmap sys pid (Some addr) size prot flags = inl (vaddr, new_sys) ->
  vaddr = addr.

(** Protection flags are properly set in the page table entries *)
Theorem mmap_protection_set : forall {S: PageSize} (sys: SystemState S) pid addr size prot flags vaddr new_sys proc pte,
  mmap sys pid addr size prot flags = inl (vaddr, new_sys) ->
  In proc (processes S new_sys) ->
  proc_id proc = pid ->
  In pte (proc_page_table proc) ->
  Z.ge (pte_virt_addr pte) vaddr ->
  Z.lt (pte_virt_addr pte) (Z.add vaddr (align_up size S)) ->
  pte_flags pte = prot_to_ptflags prot.

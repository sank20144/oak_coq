From stdpp Require Import base list propset gmap.
From Coq Require Import Logic.Classical_Prop.

Import ListNotations.

(* Address and memory types *)
Definition p_addr := nat.    (* Physical address *)
Definition v_addr := nat.    (* Virtual address *)

(* Core data structures *)
Record PageTable := {
  pt_entries : list (v_addr * p_addr);  (* List of virtual to physical address mappings *)
}.

(* Process representation *)
Record Process := {
  p_pml4 : PageTable;    (* Page table root *)
  p_pid : nat;           (* Process ID *)
}.

(* Physical memory frame *)
Record PhysFrame := {
  pf_addr : p_addr;      (* Starting physical address *)
}.

(* Virtual memory page *)
Record VirtPage := {
  vp_addr : v_addr;      (* Starting virtual address *)
  vp_owner : option Process;  (* Process that owns this page *)
}.

(* Range of physical frames *)
Record PhysFrameRange := {
  pfr_start : PhysFrame;  (* First frame in range *)
  pfr_end : PhysFrame;    (* Last frame in range *)
}.

(* Helper function for checking if an entry exists in a page table *)
Fixpoint has_mapping_aux (entries: list (v_addr * p_addr)) (va: v_addr) : bool :=
  match entries with
  | [] => false
  | (v, _) :: rest => 
      if Nat.eqb v va 
      then true
      else has_mapping_aux rest va
  end.

(* Check if an entry exists in a page table *)
Definition has_mapping (pt: PageTable) (va: v_addr) : bool :=
  has_mapping_aux pt.(pt_entries) va.

(* Helper function for looking up a physical address *)
Fixpoint translate_addr_aux (entries: list (v_addr * p_addr)) (va: v_addr) : option p_addr :=
  match entries with
  | [] => None
  | (v, p) :: rest => 
      if Nat.eqb v va 
      then Some p
      else translate_addr_aux rest va
  end.

(* Look up a physical address for a given virtual address *)
Definition translate_addr (pt: PageTable) (va: v_addr) : option p_addr :=
  translate_addr_aux pt.(pt_entries) va.

(* Add a mapping to a page table *)
Definition add_mapping (pt: PageTable) (va: v_addr) (pa: p_addr) : PageTable :=
  (* Remove existing mapping for this VA if it exists *)
  let filtered := filter (fun mapping => negb (Nat.eqb (fst mapping) va)) pt.(pt_entries) in
  {| pt_entries := (va, pa) :: filtered |}.

(* Remove a mapping from a page table *)
Definition remove_mapping (pt: PageTable) (va: v_addr) : PageTable :=
  {| pt_entries := filter (fun mapping => negb (Nat.eqb (fst mapping) va)) pt.(pt_entries) |}.


(* Create a new empty page table *)
Definition empty_page_table : PageTable := {| pt_entries := [] |}.

(* Frame equality check - two frames are equal if they have the same address *)
Definition frame_eq (f1 f2: PhysFrame) : bool :=
  Nat.eqb f1.(pf_addr) f2.(pf_addr).

(* Check if a frame is in a list of frames *)
Fixpoint frame_in_list (frame: PhysFrame) (frames: list PhysFrame) : bool :=
  match frames with
  | [] => false
  | curr :: rest => 
      if frame_eq frame curr then true
      else frame_in_list frame rest
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

(* Find owner of a frame *)
Fixpoint get_frame_owner (frame: PhysFrame) (owners: list (PhysFrame * Process)) : option Process :=
  match owners with
  | [] => None
  | (curr_frame, curr_proc) :: rest => 
      if frame_eq frame curr_frame
      then Some curr_proc
      else get_frame_owner frame rest
  end.

(* Set frame owner *)
Fixpoint set_frame_owner (frame: PhysFrame) (proc: Process) 
                        (owners: list (PhysFrame * Process)) 
                        : list (PhysFrame * Process) :=
  match owners with
  | [] => [(frame, proc)]  
  | (curr_frame, curr_proc) :: rest =>
      if frame_eq frame curr_frame
      then (frame, proc) :: rest
      else (curr_frame, curr_proc) :: set_frame_owner frame proc rest
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

(* Main allocator structure *)
Record BitmapAllocator := {
  valid_frames : list PhysFrame;         (* All valid frames *)
  allocated_frames : list PhysFrame;     (* Currently allocated frames *)
  frame_owners : list (PhysFrame * Process); (* Frame -> Process mapping *)
  range : PhysFrameRange;                (* Range of valid addresses *)
  
  (* Invariant: all valid frames are within the specified range *)
  inv_valid_frames_in_range :
    forall f, frame_in_list f valid_frames = true ->
      f.(pf_addr) >= range.(pfr_start).(pf_addr) /\
      f.(pf_addr) <= range.(pfr_end).(pf_addr);
}.

(* Total system state representation *)
Record SystemState := {
  processes: list Process;        (* All processes in the system *)
  memory_state: BitmapAllocator; (* Current memory allocator state *)
}.

(* Allocation operation *)
Program Definition allocate_frame (state: BitmapAllocator) (proc: Process) (frame: PhysFrame) 
                                 : option BitmapAllocator :=
  (* Check if frame is valid and not already allocated *)
  if andb (frame_in_list frame state.(valid_frames))
          (negb (frame_in_list frame state.(allocated_frames)))
  then 
    Some {|
      valid_frames := state.(valid_frames);
      allocated_frames := frame :: state.(allocated_frames);
      frame_owners := set_frame_owner frame proc state.(frame_owners);
      range := state.(range);  
    |}
  else None.
Next Obligation.
  intros. apply state.(inv_valid_frames_in_range). exact H.
Qed.

(* Deallocation operation *)
Program Definition deallocate_frame (state: BitmapAllocator) (frame: PhysFrame) 
                                   : option BitmapAllocator :=
  (* Check if frame is valid and currently allocated *)
  if andb (frame_in_list frame state.(valid_frames))
          (frame_in_list frame state.(allocated_frames))
  then 
    Some {|
      valid_frames := state.(valid_frames);
      allocated_frames := remove_frame frame state.(allocated_frames);
      frame_owners := remove_frame_owner frame state.(frame_owners);
      range := state.(range);
    |}
  else None.
Next Obligation.
  intros. apply state.(inv_valid_frames_in_range). exact H.
Qed.

(* Find a free frame *)
Fixpoint find_free_frame_in_list (valid_frames: list PhysFrame) 
                                (allocated_frames: list PhysFrame) 
                                : option PhysFrame :=
  match valid_frames with
  | [] => None 
  | curr :: rest =>
      if frame_in_list curr allocated_frames
      then find_free_frame_in_list rest allocated_frames
      else Some curr
  end.

Definition find_free_frame (state: BitmapAllocator) : option PhysFrame :=
  find_free_frame_in_list state.(valid_frames) state.(allocated_frames).

(* Allocate multiple frames - For the mmap function *)
Fixpoint allocate_frames (n: nat) (state: BitmapAllocator) (proc: Process) 
                        : option BitmapAllocator :=
  match n with
  | 0 => Some state 
  | S n' =>
      match find_free_frame state with
      | None => None 
      | Some frame =>
          match allocate_frame state proc frame with
          | None => None 
          | Some new_state => allocate_frames n' new_state proc
          end
      end
  end.

(* Check if a virtual address is free (not mapped) in a page table *)
Definition is_vaddr_free (pt: PageTable) (va: v_addr) : bool :=
  match translate_addr pt va with
  | None => true   (* Address is free *)
  | Some _ => false  (* Address is already mapped *)
  end.

(* Check if a range of virtual addresses is free in a page table *)
Fixpoint validate_vaddr_range (pt: PageTable) (start_va: v_addr) (size: nat) : bool :=
  match size with
  | 0 => true
  | S n' => 
      if is_vaddr_free pt start_va 
      then validate_vaddr_range pt (start_va + 1) n'
      else false  (* Found an address that's already mapped *)
  end.

Compute (validate_vaddr_range empty_page_table 0 5). (* Expected output: true *)
Compute (validate_vaddr_range {| pt_entries := [(0, 1); (1, 2)] |} 0 5). (* Expected output: false *)


(* Map a list of physical frames to virtual addresses in a process page table *)
Fixpoint map_frames_to_vaddr (pt: PageTable) (start_va: v_addr) 
                            (frames: list PhysFrame) : PageTable :=
  match frames with
  | [] => pt
  | frame :: rest =>
      let new_pt := add_mapping pt start_va frame.(pf_addr) in
      map_frames_to_vaddr new_pt (start_va + 1) rest
  end.

(* Helper function to update a process in the process list *)
Fixpoint update_process (procs: list Process) (proc: Process) : list Process :=
  match procs with
  | [] => [proc]
  | p :: rest =>
      if Nat.eqb p.(p_pid) proc.(p_pid)
      then proc :: rest
      else p :: update_process rest proc
  end.

Definition mmap (sys: SystemState) (proc: Process) (hint_addr: v_addr) 
                (size: nat)  
                : option SystemState :=
  (* First check if the virtual address range is free *)
  if validate_vaddr_range proc.(p_pml4) hint_addr size then
    (* Proceed with allocation only if the range is free *)
    match allocate_frames size sys.(memory_state) proc with
    | None => None  (* Failed to allocate enough frames *)
    | Some new_mem_state =>
        (* Determine the starting virtual address *)
        let start_va := hint_addr in
        
        (* Get all allocated frames to map them *)
        let allocated := firstn size new_mem_state.(allocated_frames) in
        
        (* Map the frames to virtual addresses in the process page table *)
        let new_pml4 := map_frames_to_vaddr proc.(p_pml4) start_va allocated in
        
        (* Create updated process with the new page table *)
        let new_proc := {| p_pml4 := new_pml4; p_pid := proc.(p_pid) |} in
        
        Some {|
          processes := update_process sys.(processes) new_proc;
          memory_state := new_mem_state;
        |}
    end
  else
    None.

Compute (mmap {| 
  processes := []; 
  memory_state := {| 
    valid_frames := [
      {| pf_addr := 0 |};
      {| pf_addr := 1 |};
      {| pf_addr := 2 |};
      {| pf_addr := 3 |};
      {| pf_addr := 4 |}
    ]; 
    allocated_frames := []; 
    frame_owners := []; 
    range := {| 
      pfr_start := {| pf_addr := 0 |}; 
      pfr_end := {| pf_addr := 100 |} 
    |} 
  |} |} 
  {| p_pml4 := empty_page_table; p_pid := 1 |} 0 5).   

(* =========== THEOREMS ============== *)
(* ==================================== *)

Section SupportLemmas.
  (* Support lemmas for the page table operations *)
  Lemma has_mapping_empty:
    forall va, has_mapping empty_page_table va = false.
  Proof.
    intros. unfold empty_page_table, has_mapping. simpl. reflexivity.
  Qed.

  Lemma translate_addr_empty:
    forall va, translate_addr empty_page_table va = None.
  Proof.
    intros. unfold empty_page_table, translate_addr. simpl. reflexivity.
  Qed.

  (* Support lemmas for records *)
  Lemma PhysFrame_eq:
  forall f1 f2, f1 = f2 -> f1.(pf_addr) = f2.(pf_addr).
  Proof.
    intros f1 f2 H. rewrite H. reflexivity.
  Qed.

  Lemma PhysFrame_neq:
    forall f1 f2, f1 <> f2 -> f1.(pf_addr) <> f2.(pf_addr).
  Proof.
    intros f1 f2 H.
    contradict H. destruct f1, f2.
    simpl in *. rewrite H. reflexivity.
  Qed.

  Lemma VirtPage_eq:
    forall v1 v2, v1 = v2 -> v1.(vp_addr) = v2.(vp_addr) /\ v1.(vp_owner) = v2.(vp_owner).
  Proof.
    intros v1 v2 H. split; congruence.
  Qed.

  Lemma VirtPage_neq:
    forall v1 v2, v1 <> v2 -> v1.(vp_addr) <> v2.(vp_addr) \/ v1.(vp_owner) <> v2.(vp_owner).
  Proof.
    intros v1 v2 Hneq.
    apply not_and_or. contradict Hneq.
    destruct Hneq as [Haddr Howner].
    destruct v1 as [addr1 owner1].
    destruct v2 as [addr2 owner2].
    simpl in *. congruence.
  Qed.

  Lemma Process_eq:
    forall p1 p2, p1 = p2 -> p1.(p_pid) = p2.(p_pid).
  Proof.
    intros p1 p2 H. congruence.
  Qed.

  Lemma process_components_determine_equality:
    forall p1 p2, 
    p1.(p_pid) = p2.(p_pid) /\ p1.(p_pml4) = p2.(p_pml4) -> p1 = p2.
  Proof.
    intros p1 p2 [Hpid Hpml4].
    destruct p1 as [pml4_1 pid_1].
    destruct p2 as [pml4_2 pid_2].
    simpl in *. congruence.
  Qed.

  Lemma Process_neq_converse:
    forall p1 p2, p1.(p_pid) <> p2.(p_pid) -> p1 <> p2.
  Proof.
    intros p1 p2 Hpid.
    unfold not. intros Heq.
    apply Hpid. congruence.
  Qed.

  Lemma frame_eq_refl: 
    forall f, frame_eq f f = true.
  Proof.
    intro f. unfold frame_eq. apply Nat.eqb_refl.
  Qed.

  Lemma frame_eq_sym: 
    forall f1 f2, frame_eq f1 f2 = frame_eq f2 f1.
  Proof.
    intros f1 f2. unfold frame_eq. apply Nat.eqb_sym.
  Qed.

  Lemma frame_eq_neq:
    forall f1 f2, f1 <> f2 -> frame_eq f1 f2 = false.
  Proof.
    intros f1 f2 H.
    unfold frame_eq. apply Nat.eqb_neq.
    apply PhysFrame_neq. apply H.
  Qed.

  Lemma frame_eq_iff:
    forall f1 f2, frame_eq f1 f2 = true -> f1 = f2.
  Proof.
    intros. unfold frame_eq in H.
    apply Nat.eqb_eq in H.
    destruct f1, f2. simpl in *. congruence.
  Qed.

  Lemma frame_in_list_correct: 
    forall frame frames, frame_in_list frame (frame :: frames) = true.
  Proof.
    intros frame frames. simpl.
    rewrite frame_eq_refl. reflexivity.
  Qed.

  Lemma removed_frame_not_in_list:
  forall fs frame, frame_in_list frame (remove_frame frame fs) = false.
  Proof.
    intros fs frame.
    induction fs as [|curr_frame rest IHrest].
    - simpl. reflexivity.
    - simpl.
      destruct (frame_eq frame curr_frame) eqn:Heq.
      + apply IHrest.
      + simpl. rewrite Heq. apply IHrest.
  Qed.

  Lemma remove_frame_correct: 
    forall frame frames, frame_in_list frame (remove_frame frame (frame :: frames)) = false.
  Proof.
    intros frame frames.
    simpl. rewrite frame_eq_refl.
    apply removed_frame_not_in_list.
  Qed.

  Lemma get_frame_owner_correct: 
    forall frame proc owners, get_frame_owner frame ((frame, proc) :: owners) = Some proc.
  Proof.
    intros frame proc owners.
    simpl. rewrite frame_eq_refl. reflexivity.
  Qed.

  Lemma set_frame_owner_correct: 
    forall frame proc owners, get_frame_owner frame (set_frame_owner frame proc owners) = Some proc.
  Proof.
    intros frame proc owners.
    induction owners as [|[curr_frame curr_proc] rest IHrest].
    - simpl. rewrite frame_eq_refl. reflexivity.
    - simpl.
      destruct (frame_eq frame curr_frame) eqn:H.
      + simpl. rewrite frame_eq_refl. reflexivity.
      + simpl. rewrite H. apply IHrest.
  Qed.

Lemma remove_frame_owner_correct:
    forall frame owners,
      get_frame_owner frame (remove_frame_owner frame owners) = None.
  Proof.
    intros frame owners.
    induction owners as [|[curr_frame curr_proc] rest IHrest].
    - simpl. reflexivity.
    - simpl.
      destruct (frame_eq frame curr_frame) eqn:H.
      + apply IHrest.
      + simpl. rewrite H. apply IHrest.
Qed.

End SupportLemmas.


Section PageTableProofs.
  (* Properties about the page table operations *)
  Lemma add_mapping_correct:
    forall pt va pa,
      has_mapping (add_mapping pt va pa) va = true.
  Proof.
    intros pt va pa.
    unfold add_mapping, has_mapping.
    simpl. rewrite Nat.eqb_refl. reflexivity.
  Qed.
      
  Lemma remove_mapping_empty:
    forall va,
      remove_mapping empty_page_table va = empty_page_table.
  Proof.
    intros.
    unfold empty_page_table, remove_mapping.
    simpl. reflexivity.
  Qed.   

  Lemma remove_mapping_correct:
    forall pt va,
      has_mapping (remove_mapping pt va) va = false.
  Proof.
    intros pt va. 
    unfold remove_mapping, has_mapping.
    induction pt.(pt_entries) as [|[v p] rest IHrest].

    - simpl. reflexivity.

    - simpl in *.
      destruct (Nat.eqb v va) eqn:Heq.

      + apply Nat.eqb_eq in Heq. subst. 
        simpl. 
        (* The induction hypothesis says that there is no va in rest of the list.
        The filter removes va from the list so only rest is there.
        since va is not there the function should evaluate to false.
        So simplifying should get us exact IHrest but it doesn't. *)
      + apply Nat.eqb_neq in Heq. 
        simpl.
      
      Admitted.
      
  Lemma translate_addr_after_add:
  forall pt va pa, 
    translate_addr (add_mapping pt va pa) va = Some pa.
  Proof.
    intros.
    unfold translate_addr, add_mapping.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  Qed.

  Lemma empty_page_table_has_no_mappings:
    forall va, 
      translate_addr empty_page_table va = None.
  Proof.
    intros. 
    unfold empty_page_table. 
    simpl. reflexivity.
  Qed.

  Lemma translate_addr_correct:
    forall pt va pa pt',
      add_mapping pt va pa = pt' ->
      translate_addr pt' va = Some pa.
  Proof.
    intros. unfold add_mapping in H.
    destruct (Nat.eqb va va) eqn:Hva.
    - apply Nat.eqb_eq in Hva. subst.
      unfold translate_addr. simpl.
      rewrite Nat.eqb_refl. reflexivity.
    - apply Nat.eqb_neq in Hva. 
      contradict Hva.
      reflexivity.
  Qed.
    
  Lemma update_process_correct:
    forall procs proc,
    In proc (update_process procs proc).
  Proof.
    intros procs proc.
    induction procs as [|p rest IH].
    - simpl. left. reflexivity.
    - simpl.
      destruct (Nat.eqb (p_pid p) (p_pid proc)) eqn:Heq.
      + left. reflexivity.
      + right. apply IH.
  Qed.

  Lemma mmap_correct:
    forall sys proc hint_addr size new_sys,
      mmap sys proc hint_addr size = Some new_sys ->
      exists new_proc, In new_proc new_sys.(processes) /\
        new_proc.(p_pid) = proc.(p_pid) /\
        validate_vaddr_range new_proc.(p_pml4) hint_addr size = false.
  Proof.
  Admitted.

End PageTableProofs.

Section BitmapAllocatorProofs.
  
  Lemma allocate_frame_correct: 
    forall state state1 proc frame,
      allocate_frame state proc frame = Some state1 ->
      frame_in_list frame state1.(allocated_frames) = true.
  Proof.
    intros state state1 proc frame H.
    unfold allocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (negb (frame_in_list frame state.(allocated_frames)))) eqn:Hcond.
    
    - injection H as H_eq.
      subst state1.
      simpl.
      rewrite frame_eq_refl.
      reflexivity.
      
    - discriminate H.
  Qed.

  Lemma dealloc_correct:
    forall state state1 frame,
      deallocate_frame state frame = Some state1 ->
      frame_in_list frame state1.(allocated_frames) = false.
  Proof.
    intros state state1 frame H.
    unfold deallocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (frame_in_list frame state.(allocated_frames))) eqn:Hcond.
    - injection H as H_eq.
      subst state1.
      simpl.
      apply removed_frame_not_in_list.
    - discriminate H.
  Qed.

  (* No double allocation theorem *)
  Theorem no_double_allocation: 
    forall state state1 p1 p2 frame,
      p1.(p_pid) <> p2.(p_pid) ->
      allocate_frame state p1 frame = Some state1 ->
      allocate_frame state1 p2 frame = None.
  Proof.
    intros state state1 p1 p2 frame H Halloc.
    unfold allocate_frame in Halloc.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (negb (frame_in_list frame state.(allocated_frames)))) eqn:Hcond.
    - injection Halloc as H_eq.
      subst state1.

      unfold allocate_frame.
      simpl.

      rewrite frame_eq_refl.
      simpl.
      rewrite andb_false_r.
      reflexivity.
    - discriminate Halloc.
  Qed.

  (* Allocation constraints *)
  Theorem unallocated_frames_only_alloc:
    forall state state1 proc frame,
      allocate_frame state proc frame = Some state1 ->
      frame_in_list frame state.(allocated_frames) = false.
  Proof.
    intros state state1 proc frame H.
    unfold allocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (negb (frame_in_list frame state.(allocated_frames)))) eqn:Hcond.
    - injection H as H_eq.
      apply andb_prop in Hcond.
      destruct Hcond as [_ Hnot_allocated].
      apply negb_true_iff in Hnot_allocated.
      exact Hnot_allocated.
    - discriminate H.
  Qed.

  Theorem valid_frames_only_alloc: 
    forall state state1 proc frame,
      allocate_frame state proc frame = Some state1 ->
      frame_in_list frame state.(valid_frames) = true.
  Proof.
    intros state state1 proc frame H.
    unfold allocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (negb (frame_in_list frame state.(allocated_frames)))) eqn:Hcond.
    - injection H as H_eq.
      apply andb_prop in Hcond.
      destruct Hcond as [Hvalid _].
      exact Hvalid.
    - discriminate H.
  Qed.

  (* Combined allocation theorem *)
  Theorem valid_unallocated_frames_only_alloc:
    forall state state1 proc frame,
      allocate_frame state proc frame = Some state1 ->
      frame_in_list frame state.(valid_frames) = true /\
      frame_in_list frame state.(allocated_frames) = false.
  Proof.
    intros state state1 proc frame H.
    split.
    - apply valid_frames_only_alloc in H. exact H.
    - apply unallocated_frames_only_alloc in H. exact H.
  Qed.

  (* Deallocation constraints *)
  Theorem allocated_frames_only_dealloc: 
    forall state state1 frame,
      deallocate_frame state frame = Some state1 ->
      frame_in_list frame state.(allocated_frames) = true.
  Proof.
    intros state state1 frame H.
    unfold deallocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (frame_in_list frame state.(allocated_frames))) eqn:Hcond.
    - injection H as H_eq.
      apply andb_prop in Hcond.
      destruct Hcond as [_ Hallocated].
      exact Hallocated.
    - discriminate H.
  Qed.

  Theorem valid_frames_only_dealloc:
    forall state state1 frame,
      deallocate_frame state frame = Some state1 ->
      frame_in_list frame state.(valid_frames) = true.
  Proof.
    intros state state1 frame H.
    unfold deallocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (frame_in_list frame state.(allocated_frames))) eqn:Hcond.
    - injection H as H_eq.
      apply andb_prop in Hcond.
      destruct Hcond as [Hvalid _].
      exact Hvalid.
    - discriminate H.
  Qed.

  (* Combined deallocation theorem *)
  Theorem valid_allocated_frames_only_dealloc: 
    forall state state1 frame,
      deallocate_frame state frame = Some state1 ->
      frame_in_list frame state.(valid_frames) = true /\
      frame_in_list frame state.(allocated_frames) = true.
  Proof.
    intros state state1 frame H.
    split.
    - apply valid_frames_only_dealloc in H. exact H.
    - apply allocated_frames_only_dealloc in H. exact H.
  Qed.

  (* Range checking *)
  Theorem bitmapallocator_only_allocates_in_range:
    forall state state1 proc frame,
      allocate_frame state proc frame = Some state1 ->
      frame.(pf_addr) >= state.(range).(pfr_start).(pf_addr) /\
      frame.(pf_addr) <= state.(range).(pfr_end).(pf_addr).
  Proof.
    intros state state1 proc frame H.
    unfold allocate_frame in H.
    destruct (andb (frame_in_list frame state.(valid_frames))
                  (negb (frame_in_list frame state.(allocated_frames)))) eqn:Hcond.
    
    - injection H as H_eq.
      apply andb_prop in Hcond.
      destruct Hcond as [Hvalid _].
      apply state.(inv_valid_frames_in_range).
      exact Hvalid.
      
    - discriminate H.
  Qed.

End BitmapAllocatorProofs.

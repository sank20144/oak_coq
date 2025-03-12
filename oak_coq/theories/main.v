From stdpp Require Import base list propset gmap.
(* Compute 5. *)

Section sec.
  Context
    (ProcessT : Set)
    (FrameT : Set)
  .

  Record AbstractKernelState1 := {
    has_access : ProcessT -> FrameT -> Prop ;
    invariant_1 :
      forall (p1 p2 : ProcessT) (f : FrameT), 
      has_access p1 f -> has_access p2 f -> p1 = p2 ;
  }.

  Definition frame_is_allocated
    (s : AbstractKernelState1)
    (f : FrameT)
    : Prop
  :=
    exists p, has_access s p f
  .

  Definition AllocFrameFun : Type :=
    AbstractKernelState1 ->
    ProcessT ->
    option (AbstractKernelState1*FrameT)
  .

  Definition AllocFrameFun_spec
    : AllocFrameFun -> Prop
  :=
    fun alloc =>
      forall (s s' : AbstractKernelState1)
        (p : ProcessT)
        (f : FrameT),
        alloc s p = Some (s',f) ->
          has_access s' p f
  .

End sec.

Section impl.
    Definition ProcessT := nat.
    Definition FrameT := nat.

    Record ConcreteKernelState := {
      available_frames : list FrameT;
      allocated_frames : gmap FrameT ProcessT ;
  }.

  Program Definition abstract_of (s : ConcreteKernelState)
    : AbstractKernelState1 ProcessT FrameT := {|
    has_access := fun p f =>
      match (allocated_frames s) !! f with
      | Some p' => p = p'
      | None => False
      end
  |}.
  Next Obligation.
    intros s p1 p2 f. simpl in *.
    destruct (allocated_frames s !! f) eqn:Heq1.
    {
      intros H1 H2. congruence.
    }
    {
      intros H1 H2. inversion H1.
    }
  Qed.

End impl.

(* 
Program Definition make_initial_state
  (Frames: Set)
  (Processes: Set)
  : AbstractKernelState1 := {|
  FrameT := Frames;
  ProcessT := Processes;
  has_access := fun _ _ => False ;
|}.
Next Obligation.
  intros. simpl in *. inversion H.
Qed.
Fail Next Obligation.

Definition AbstractKernelState1_step
: AbstractKernelState1 -> AbstractKernelState1 -> Prop :=
  fun a b => True
.

Record AbstractKernelState2 := {
  ProcessT2 : Set ;
  FrameT2 : Set ;
  has_access2 : ProcessT2 -> FrameT2 -> Prop ;
  invariant_21 :
    forall (p1 p2 : ProcessT) (f : FrameT), 
    has_access p1 f -> has_access p2 f -> p1 = p2 ;
}. *)

Record FileDescriptor := {
    fd_num : nat ;
}.

Inductive Syscall :=
| sc_read (fd : FileDescriptor) : Syscall
| sc_write (fd : FileDescriptor) : Syscall
| sc_mmap : Syscall
| sc_fsync : Syscall
| sc_exit : Syscall
.

Record Process := {
  (* TODO *)
}.

Record KernelState := {
  ks_processes : list Process ;
}.

Inductive HwInterrupt :=
| hi_systick
.

Inductive Event :=
| e_syscall (sc : Syscall)
| e_hw_interrupt (hi : HwInterrupt)
.

Inductive Effect :=
| ef_none
(* | ef_toggle_led *)
.

Inductive kernel_step :
    Event -> KernelState -> KernelState -> Effect -> Prop
:=
| ev_systick_interrupt:
    forall (ks : KernelState),
        kernel_step (e_hw_interrupt hi_systick) ks ks ef_none
| ks_syscall :
    forall (sc : Syscall) (ks: KernelState), kernel_step ks ks
.

(* Check ev_systick_interrupt. *)

Compute (sc_read {|fd_num := 5|}).
(* 
Lemma sc_read_from_5_does_nothing:
    forall (state : KernelState),
        kernel_step state 
.
Compute (sc_read {|fd_num := 5|}).

Check ks_syscall.
 *)

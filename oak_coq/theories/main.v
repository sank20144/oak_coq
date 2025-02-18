From stdpp Require Import base list.
(* Compute 5. *)

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

Require Import Coq.ZArith.ZArith.
Require Import ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Import ListNotations.
From OC Require Import PhysicalMemory.
From OC Require Import BitArr.
From OC Require Import MemoryModel.
From OC Require Import BitmapAllocatorCore.

Section BitmapAllocator.

    (** Generic axioms for converting between any type and value *)
    Axiom type_to_value : forall {T : Type}, T -> value.
    Axiom value_to_type : forall {T : Type}, value -> option T.

    (** Generic roundtrip property *)
    Axiom value_roundtrip : forall {T : Type} (x : T),
        value_to_type (type_to_value x) = Some x.

    (** Generic store function *)
    Definition store {T : Type} (m : memory) (x : T) : memory * addr :=
        MemoryModel.alloc m (type_to_value x).

    (** Generic load function *)
    Definition load {T : Type} (m : memory) (a : addr) : option T :=
        match read m a with
        | Some v => value_to_type v
        | None => None
        end.

    (** Initialize allocator in empty memory *)
    Definition init_allocator {S : PageSize} {n : nat}
        (r : PhysFrameRange S) : memory * addr :=
        let allocator := new_allocator n r in
        store empty_memory allocator.

End BitmapAllocator.

Section BitmapFrameAllocator.

Definition allocate_frame {S : PageSize} {n : nat}
        (m : memory) (bitmapAllocAddr : addr) : option (memory * PhysFrame S * lifetime) :=
        (* 1. Create mutable borrow of allocator *)
        match borrow_mut m bitmapAllocAddr with
        | Some (m1, lt) =>
            (* 2. Load allocator through borrow *)
            match load m1 bitmapAllocAddr with
            | Some alloc =>
                (* 3. Find first available frame *)
                match first_one_from_zero (get_available alloc) with
                | Some idx =>
                    match idx_to_frame alloc idx with
                    | Some frame =>
                        (* 4. Update allocator's allocated bitmap *)
                        let new_allocated := set_bit (allocated S n alloc) idx true in
                        let alloc' := mkBitmapAllocator S n new_allocated 
                                                        (valid S n alloc)
                                                        (range S n alloc) in
                        (* 5. Write updated allocator back through mutable borrow *)
                        match write m1 bitmapAllocAddr (type_to_value alloc') with
                        | Some m2 =>
                            (* 6. End the mutable borrow *)
                            match end_borrow m2 lt with
                            | Some m3 => Some (m3, frame, lt)
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None  (* No available frames *)
                end
            | None => None
            end
        | None => None  (* Cannot create mutable borrow *)
        end.


End BitmapFrameAllocator.
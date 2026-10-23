(** * Stage 10 exercises — the same moves, in Rocq

    Replace each [Admitted.] with a proof ending in [Qed.].
    Check with [make -C rocq]. Solutions: [Solutions.v]. *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.
From Metal Require Import Machine.

(** ** E10.1 ★ Reverse with an accumulator (Lean: E2.9).
    Generalise over [acc] before you induct: [induction xs as [| x xs IH]; intros acc]. *)
Fixpoint rev_acc {A : Type} (acc xs : list A) : list A :=
  match xs with
  | [] => acc
  | x :: xs => rev_acc (x :: acc) xs
  end.

Lemma rev_acc_eq : forall (A : Type) (xs acc : list A), rev_acc acc xs = rev xs ++ acc.
Proof.
Admitted.

(** ** E10.2 ★★ Differential: tail-recursive zero count = naive count (Lean: E2.10).
    In the [cons] case, [destruct (Nat.eqb x 0)] and finish with [lia]. *)
Fixpoint count_z (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => (if Nat.eqb x 0 then 1 else 0) + count_z xs
  end.

Fixpoint count_z_acc (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => count_z_acc (if Nat.eqb x 0 then acc + 1 else acc) xs
  end.

Lemma count_z_acc_eq : forall xs acc, count_z_acc acc xs = acc + count_z xs.
Proof.
Admitted.

(** ** E10.3 ★★ A variant program never crashes.
    [sum2_prog] adds every byte twice (one extra [Add]). Prove it exits cleanly
    on every input. Copy [loop] and [sum_exits_cleanly] from [Machine.v] and
    adjust: there's one more instruction per iteration, and the targets moved. *)
Definition sum2_prog : list instr :=
  [ Li R0 0           (* 0 *)
  ; Li R2 0           (* 1 *)
  ; Beq R0 R1 8       (* 2 *)
  ; Load R3 R0        (* 3 *)
  ; Add R2 R2 R3      (* 4 *)
  ; Add R2 R2 R3      (* 5 *)
  ; AddI R0 R0 1      (* 6 *)
  ; Jmp 2             (* 7 *)
  ; Halt R2 ].        (* 8 *)

Theorem sum2_exits_cleanly : forall mem, exits_cleanly sum2_prog mem (init mem).
Proof.
Admitted.

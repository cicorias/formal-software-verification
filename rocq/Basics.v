(** * Stage 10a — Stage 2 again, in Rocq

    The same definitions and proofs as [Metal/S02_Proofs.lean], so you can
    read them side by side. Rocq is the prover the article used; most of what
    you learned transfers word for word. See [docs/10-rocq-and-the-real-thing.md]
    for the translation table. *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(** Lean: [def sumList : List Nat → Nat | [] => 0 | x :: xs => x + sumList xs] *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Fixpoint sum_acc (acc : nat) (l : list nat) : nat :=
  match l with
  | [] => acc
  | x :: xs => sum_acc (acc + x) xs
  end.

(** Computation: Lean's [rfl]/[decide] is [reflexivity]/[vm_compute]. *)
Example sum_example : sum_list [1; 2; 3; 4] = 10.
Proof. reflexivity. Qed.

(** Induction. Lean: [induction xs with | nil => … | cons x xs ih => …].
    [lia] is Rocq's [omega]: linear arithmetic over [nat] and [Z]. *)
Lemma sum_list_app : forall xs ys, sum_list (xs ++ ys) = sum_list xs + sum_list ys.
Proof.
  induction xs as [| x xs IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** The accumulator lemma, generalised over [acc] — exactly Stage 2 §5.
    In Rocq you generalise by putting [acc] after the induction variable and
    re-introducing it ([intros acc]) in each case. *)
Lemma sum_acc_eq : forall xs acc, sum_acc acc xs = acc + sum_list xs.
Proof.
  induction xs as [| x xs IH]; intros acc; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Theorem sum_acc_correct : forall xs, sum_acc 0 xs = sum_list xs.
Proof. intros xs. rewrite sum_acc_eq. reflexivity. Qed.

(** A counterexample is a proof of a negation, here as in Lean. *)
Example not_all_grow : ~ (forall n : nat, n * 2 > n).
Proof. intros H. specialize (H 0). simpl in H. lia. Qed.

(** Lean's [#print axioms] is Rocq's [Print Assumptions]. *)
Print Assumptions sum_acc_correct.   (* "Closed under the global context" *)

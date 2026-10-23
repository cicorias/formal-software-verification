(** * Stage 10 solutions *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.
From Metal Require Import Machine.

Fixpoint rev_acc {A : Type} (acc xs : list A) : list A :=
  match xs with
  | [] => acc
  | x :: xs => rev_acc (x :: acc) xs
  end.

Lemma rev_acc_eq : forall (A : Type) (xs acc : list A), rev_acc acc xs = rev xs ++ acc.
Proof.
  intros A xs. induction xs as [| x xs IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH, <- app_assoc. reflexivity.
Qed.

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
  induction xs as [| x xs IH]; intros acc; simpl.
  - lia.
  - rewrite IH. destruct (Nat.eqb x 0); lia.
Qed.

Definition sum2_prog : list instr :=
  [ Li R0 0; Li R2 0; Beq R0 R1 8; Load R3 R0; Add R2 R2 R3; Add R2 R2 R3;
    AddI R0 R0 1; Jmp 2; Halt R2 ].

Lemma loop2 : forall mem k s,
    pc s = 2 -> regs s R1 = length mem -> regs s R0 + k = length mem ->
    exists s' c, star sum2_prog mem s s' /\ sstep sum2_prog mem s' (SHalt c).
Proof.
  intros mem k. induction k as [| k IH]; intros [p rg] Hpc Hlen Hk;
    simpl in Hpc, Hlen, Hk; subst p.
  - exists (mk 8 rg), (rg R2). split.
    + apply star_step with (s2 := mk 8 rg); [| apply star_refl].
      apply s_beq_taken with (r1 := R0) (r2 := R1); [reflexivity | simpl; lia].
    + exact (s_halt sum2_prog mem (mk 8 rg) R2 eq_refl).
  - destruct (nth_error mem (rg R0)) as [v |] eqn:Hv.
    2: { apply nth_error_None in Hv. lia. }
    set (s4 := set (mk 3 rg) R3 v 4).
    set (s5 := set s4 R2 (regs s4 R2 + regs s4 R3) 5).
    set (s6 := set s5 R2 (regs s5 R2 + regs s5 R3) 6).
    set (s7 := set s6 R0 (regs s6 R0 + 1) 7).
    destruct (IH (mk 2 (regs s7))) as [s' [c [Hstar Hhalt]]];
      [reflexivity | simpl; exact Hlen | simpl; lia |].
    exists s', c. split; [| exact Hhalt].
    apply star_step with (s2 := mk 3 rg).
    { apply s_beq_not with (r1 := R0) (r2 := R1) (t := 8); [reflexivity | simpl; lia]. }
    apply star_step with (s2 := s4).
    { apply s_load_ok with (rd := R3) (rs := R0); [reflexivity | exact Hv]. }
    apply star_step with (s2 := s5).
    { apply s_add with (rd := R2) (r1 := R2) (r2 := R3). reflexivity. }
    apply star_step with (s2 := s6).
    { apply s_add with (rd := R2) (r1 := R2) (r2 := R3). reflexivity. }
    apply star_step with (s2 := s7).
    { apply s_addi with (rd := R0) (rs := R0) (n := 1). reflexivity. }
    apply star_step with (s2 := mk 2 (regs s7)).
    { apply s_jmp with (t := 2). reflexivity. }
    exact Hstar.
Qed.

Theorem sum2_exits_cleanly : forall mem, exits_cleanly sum2_prog mem (init mem).
Proof.
  intros mem.
  set (s2 := mk 2 (regs (set (set (init mem) R0 0 1) R2 0 2))).
  destruct (loop2 mem (length mem) s2) as [s' [c [Hstar Hhalt]]];
    [reflexivity | reflexivity | reflexivity |].
  exists s', c. split; [| exact Hhalt].
  eapply star_step. { apply s_li with (rd := R0) (n := 0). reflexivity. }
  eapply star_step. { apply s_li with (rd := R2) (n := 0). reflexivity. }
  exact Hstar.
Qed.

Print Assumptions sum2_exits_cleanly.

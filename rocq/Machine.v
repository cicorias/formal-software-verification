(** * Stage 10b — A machine, the way the article's model is written

    [Metal/S05_Machine.lean] defines the semantics as a *function*
    ([step : Machine → Outcome]) and runs it with fuel. The real model,
    theorem-labs/rocq-linux-process-semantics, defines it as a *relation*:

      Inductive sstep : config -> list event -> step_to -> Prop := ...
      Inductive star  : config -> list event -> config -> Prop := ...

    with [step_to = SNext c | SError]. A relation can say "the kernel may
    return any non-empty prefix of the input to [read]" — several possible
    next states — which a function can't. That nondeterminism is why their
    statements quantify over *all* executions.

    This file is that shape in miniature: a toy register machine (registers
    hold unbounded [nat]s — the Lean course does the bit-vectors), a
    relational [sstep] with an [SError] outcome for out-of-bounds loads, a
    [star] closure, and a proof that a summing loop exits cleanly on every
    input. Same proof structure as Stage 6: invariant, induction on the
    iterations left, done. *)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

Inductive reg := R0 | R1 | R2 | R3.

Definition reg_eqb (a b : reg) : bool :=
  match a, b with
  | R0, R0 | R1, R1 | R2, R2 | R3, R3 => true
  | _, _ => false
  end.

Inductive instr :=
| Li   (rd : reg) (n : nat)              (* rd := n *)
| AddI (rd rs : reg) (n : nat)           (* rd := rs + n *)
| Add  (rd rs1 rs2 : reg)                (* rd := rs1 + rs2 *)
| Load (rd rs : reg)                     (* rd := mem[rs], or fault *)
| Beq  (rs1 rs2 : reg) (target : nat)    (* if rs1 = rs2 then pc := target *)
| Jmp  (target : nat)
| Halt (rs : reg).                       (* exit(rs) *)

Record state := mk { pc : nat; regs : reg -> nat }.

Definition set (s : state) (r : reg) (v : nat) (pc' : nat) : state :=
  mk pc' (fun r' => if reg_eqb r' r then v else regs s r').

Inductive step_to :=
| SNext (s : state)
| SHalt (code : nat)
| SError.

Section Semantics.
Variable prog : list instr.
Variable mem : list nat.          (* the input buffer; the only readable memory *)

(** One rule per instruction (and per outcome). Read it like the RISC-V manual. *)
Inductive sstep : state -> step_to -> Prop :=
| s_li : forall s rd n,
    nth_error prog (pc s) = Some (Li rd n) ->
    sstep s (SNext (set s rd n (S (pc s))))
| s_addi : forall s rd rs n,
    nth_error prog (pc s) = Some (AddI rd rs n) ->
    sstep s (SNext (set s rd (regs s rs + n) (S (pc s))))
| s_add : forall s rd r1 r2,
    nth_error prog (pc s) = Some (Add rd r1 r2) ->
    sstep s (SNext (set s rd (regs s r1 + regs s r2) (S (pc s))))
| s_load_ok : forall s rd rs v,
    nth_error prog (pc s) = Some (Load rd rs) ->
    nth_error mem (regs s rs) = Some v ->
    sstep s (SNext (set s rd v (S (pc s))))
| s_load_fault : forall s rd rs,                  (* the AddressSanitizer rule *)
    nth_error prog (pc s) = Some (Load rd rs) ->
    nth_error mem (regs s rs) = None ->
    sstep s SError
| s_beq_taken : forall s r1 r2 t,
    nth_error prog (pc s) = Some (Beq r1 r2 t) ->
    regs s r1 = regs s r2 ->
    sstep s (SNext (mk t (regs s)))
| s_beq_not : forall s r1 r2 t,
    nth_error prog (pc s) = Some (Beq r1 r2 t) ->
    regs s r1 <> regs s r2 ->
    sstep s (SNext (mk (S (pc s)) (regs s)))
| s_jmp : forall s t,
    nth_error prog (pc s) = Some (Jmp t) ->
    sstep s (SNext (mk t (regs s)))
| s_halt : forall s r,
    nth_error prog (pc s) = Some (Halt r) ->
    sstep s (SHalt (regs s r)).

(** Reflexive-transitive closure of [SNext] steps (theirs also collects events). *)
Inductive star : state -> state -> Prop :=
| star_refl : forall s, star s s
| star_step : forall s1 s2 s3, sstep s1 (SNext s2) -> star s2 s3 -> star s1 s3.

(** The spec shape: we can reach a state whose next step is a clean exit.
    (Our [sstep] is deterministic, so that also rules out every fault. In a
    nondeterministic model you'd need "every execution", which is what
    theorem-labs' [strong_universal_*] statements say.) *)
Definition exits_cleanly (s0 : state) : Prop :=
  exists s c, star s0 s /\ sstep s (SHalt c).

End Semantics.

(** The program: sum the input buffer. R1 holds its length on entry. *)
Definition sum_prog : list instr :=
  [ Li R0 0           (* 0: p = 0                  *)
  ; Li R2 0           (* 1: s = 0                  *)
  ; Beq R0 R1 7       (* 2: if p == len goto 7     *)
  ; Load R3 R0        (* 3: t = mem[p]   ← can it fault? *)
  ; Add R2 R2 R3      (* 4: s += t                 *)
  ; AddI R0 R0 1      (* 5: p++                    *)
  ; Jmp 2             (* 6: loop                   *)
  ; Halt R2 ].        (* 7: exit(s)                *)

Definition init (mem : list nat) : state :=
  mk 0 (fun r => match r with R1 => length mem | _ => 0 end).

(** The loop, by induction on the iterations left (Lean: [loop_all]). *)
Lemma loop : forall mem k s,
    pc s = 2 ->
    regs s R1 = length mem ->
    regs s R0 + k = length mem ->
    exists s' c, star sum_prog mem s s' /\ sstep sum_prog mem s' (SHalt c).
Proof.
  intros mem k. induction k as [| k IH]; intros [p rg] Hpc Hlen Hk;
    simpl in Hpc, Hlen, Hk; subst p.
  - (* p = len: the beq is taken, then halt *)
    exists (mk 7 rg), (rg R2). split.
    + apply star_step with (s2 := mk 7 rg); [| apply star_refl].
      apply s_beq_taken with (r1 := R0) (r2 := R1); [reflexivity | simpl; lia].
    + exact (s_halt sum_prog mem (mk 7 rg) R2 eq_refl).
  - (* p < len: the load is in bounds; go round once and use IH *)
    destruct (nth_error mem (rg R0)) as [v |] eqn:Hv.
    2: { apply nth_error_None in Hv. lia. }
    (* the states after beq, load, add, addi; jmp brings us back to pc 2 *)
    set (s4 := set (mk 3 rg) R3 v 4).
    set (s5 := set s4 R2 (regs s4 R2 + regs s4 R3) 5).
    set (s6 := set s5 R0 (regs s5 R0 + 1) 6).
    destruct (IH (mk 2 (regs s6))) as [s' [c [Hstar Hhalt]]].
    + reflexivity.
    + simpl. exact Hlen.
    + simpl. lia.
    + exists s', c. split; [| exact Hhalt].
      apply star_step with (s2 := mk 3 rg).
      { apply s_beq_not with (r1 := R0) (r2 := R1) (t := 7); [reflexivity | simpl; lia]. }
      apply star_step with (s2 := s4).
      { apply s_load_ok with (rd := R3) (rs := R0); [reflexivity | exact Hv]. }
      apply star_step with (s2 := s5).
      { apply s_add with (rd := R2) (r1 := R2) (r2 := R3). reflexivity. }
      apply star_step with (s2 := s6).
      { apply s_addi with (rd := R0) (rs := R0) (n := 1). reflexivity. }
      apply star_step with (s2 := mk 2 (regs s6)).
      { apply s_jmp with (t := 2). reflexivity. }
      exact Hstar.
Qed.

(** The theorem: for every input buffer, the program exits cleanly. *)
Theorem sum_exits_cleanly : forall mem, exits_cleanly sum_prog mem (init mem).
Proof.
  intros mem.
  set (s2 := mk 2 (regs (set (set (init mem) R0 0 1) R2 0 2))).
  destruct (loop mem (length mem) s2) as [s' [c [Hstar Hhalt]]];
    [reflexivity | reflexivity | reflexivity |].
  exists s', c. split; [| exact Hhalt].
  eapply star_step. { apply s_li with (rd := R0) (n := 0). reflexivity. }
  eapply star_step. { apply s_li with (rd := R2) (n := 0). reflexivity. }
  exact Hstar.
Qed.

Print Assumptions sum_exits_cleanly.

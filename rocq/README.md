# Stage 10 — Rocq

The article's proofs are in [Rocq](https://rocq-prover.org) (the prover formerly
called Coq). These files restate the course's core ideas in Rocq so you can read
theorem-labs' code without the syntax getting in the way.

| File | What |
|---|---|
| `Basics.v` | Stage 2 in Rocq: lists, induction, the accumulator generalisation, `Print Assumptions`. |
| `Machine.v` | A machine in the *relational* style of `rocq-linux-process-semantics/theories/LinuxProcessSem/Run.v`: `sstep … (SNext s \| SHalt c \| SError)`, `star`, and a no-crash proof for a summing loop. |
| `Exercises.v` | Three exercises (`Admitted.` = Lean's `sorry`). |
| `Solutions.v` | Their solutions. |

Build: `make -C rocq` (needs Rocq 9.x and its standard library, the `rocq-stdlib`
opam package). If `rocq` says *Cannot find a physical path bound to logical path
… Stdlib*, point it at the library, e.g. with nix:
`ROCQPATH=$HOME/.nix-profile/lib/coq/9.1/user-contrib make -C rocq`.

Read `docs/10-rocq-and-the-real-thing.md` for the Lean↔Rocq translation table and
a guided tour of the real model.

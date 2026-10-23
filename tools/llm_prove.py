#!/usr/bin/env python3
"""llm_prove: the article's loop in ~150 lines -- propose, check, feed back, retry.

    untrusted search (Claude)  --proof-->  trusted check (proof_guard.py + Lean)
            ^                                         |
            +------------- errors / goals ------------+

Claude sees the frozen statement, the machine model, the proof library and
one worked proof; it writes a complete `Lab/Proof.lean`; we run the guard;
on rejection we send back the guard's output and ask for a fix. Nothing
Claude writes is trusted: the guard decides.

This is a teaching harness, not a production one. In practice you'd run
Claude Code (or the Agent SDK) in the repo with the `fv-prove` skill
(`.claude/skills/fv-prove/SKILL.md`), which gives the model a shell, the
editor, and incremental checking. Seeing the bare loop makes the
architecture -- and the token bill -- visible.

Requirements: `pip install anthropic`, and credentials in the environment
(ANTHROPIC_API_KEY, or an `ant auth login` profile).

Usage:
    python3 tools/llm_prove.py [--rounds 8] [--effort high]

Cost: every round re-sends the conversation. The large static context (spec,
model, library, example) is marked for prompt caching, so after round 1 it
is billed at the cache-read rate; the script prints the token accounting.
It only ever writes `Lab/Proof.lean` (and keeps a backup of the original).
"""
import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

import anthropic

ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / "Lab" / "Proof.lean"
MODEL = "claude-opus-5-5"

CONTEXT_FILES = [
    "Lab/Spec.lean",              # the frozen statement (what to prove)
    "Metal/S05_Machine.lean",     # the trusted machine model
    "Metal/S06_SymExec.lean",     # the proof library: lemmas + the `sym` tactic
    "Metal/S06_NoCrash.lean",     # a worked proof with the same shape
    "Metal/S08_Trust.lean",       # a worked *functional* proof (sum_correct)
]

SYSTEM = """You are a proof engineer working in Lean 4 (v4.35, no Mathlib).
You will be given a frozen theorem statement about a RISC-V program, the
machine model it refers to, a proof library, and worked examples. Your job is
to write the complete contents of the file Lab/Proof.lean so that the theorem
`Lab.main : Lab.Statement` is proved.

Rules (a checker enforces them; violations are rejected without a build):
- Do not use sorry, admit, axiom, native_decide, bv_decide, #eval, macros,
  new syntax, unsafe/partial definitions, or set_option debug.*.
- Import only Lab.Spec and modules under Metal.
- The statement in Lab/Spec.lean is fixed. Prove exactly it.

Method that works for this machine: a prologue to the loop head, a loop
invariant structure, a one-iteration lemma using `sym`, an induction on the
iterations remaining, an epilogue, glued with `run_add_of_running`. State
facts you pass to `sym` in the forms simp itself produces. Checkpoint the
machine state with an `∃ m, run ... = .running m ∧ ...` lemma rather than
symbolically executing many instructions from `load input` in one go.

Reply with one ```lean code block containing the whole file, then at most a
few sentences on what you changed."""


def static_context() -> str:
    parts = []
    for rel in CONTEXT_FILES:
        parts.append(f"=== {rel} ===\n{(ROOT / rel).read_text()}")
    return "\n\n".join(parts)


def extract_lean(text: str) -> str | None:
    blocks = re.findall(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    return blocks[-1] if blocks else None


def run_guard() -> tuple[bool, str]:
    proc = subprocess.run([sys.executable, str(ROOT / "tools" / "proof_guard.py")],
                          cwd=ROOT, capture_output=True, text=True)
    return proc.returncode == 0, (proc.stdout + proc.stderr)[-6000:]


def lean_errors() -> str:
    """The guard summarises; for repair the model needs Lean's full messages."""
    proc = subprocess.run(["lake", "build", "Lab.Proof"], cwd=ROOT, capture_output=True, text=True)
    out = "\n".join(l for l in (proc.stdout + proc.stderr).splitlines() if not l.startswith("trace"))
    return out[-12000:]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rounds", type=int, default=8)
    ap.add_argument("--effort", default="high", choices=["low", "medium", "high", "xhigh", "max"])
    args = ap.parse_args()

    backup = PROOF.with_suffix(".lean.orig")
    if not backup.exists():
        shutil.copy(PROOF, backup)

    client = anthropic.Anthropic()
    # The static prefix: identical bytes every round, so it caches.
    system = [
        {"type": "text", "text": SYSTEM},
        {"type": "text", "text": static_context(), "cache_control": {"type": "ephemeral"}},
    ]
    messages = [{"role": "user",
                 "content": f"Current Lab/Proof.lean:\n```lean\n{PROOF.read_text()}```\nWrite the proof."}]
    totals = dict(input=0, cache_write=0, cache_read=0, output=0)

    for rnd in range(1, args.rounds + 1):
        with client.beta.messages.stream(
            model=MODEL,
            max_tokens=64000,
            system=system,
            messages=messages,
            output_config={"effort": args.effort},
            betas=["server-side-fallback-2026-07-01"],
            fallbacks="default",          # if a safety classifier declines, retry server-side
        ) as stream:
            response = stream.get_final_message()

        u = response.usage
        totals["input"] += u.input_tokens
        totals["cache_write"] += u.cache_creation_input_tokens or 0
        totals["cache_read"] += u.cache_read_input_tokens or 0
        totals["output"] += u.output_tokens
        print(f"[round {rnd}] model={response.model} stop={response.stop_reason} "
              f"in={u.input_tokens} cache_w={u.cache_creation_input_tokens} "
              f"cache_r={u.cache_read_input_tokens} out={u.output_tokens}")

        if response.stop_reason == "refusal":
            print("  the request was declined:", response.stop_details)
            return 1
        if response.stop_reason == "max_tokens":
            print("  output hit max_tokens; stopping")
            return 1

        text = "".join(b.text for b in response.content if b.type == "text")
        candidate = extract_lean(text)
        # Append the assistant turn exactly as returned (thinking blocks included):
        # history must be append-only for the model to keep its reasoning.
        messages.append({"role": "assistant", "content": response.content})

        if candidate is None:
            messages.append({"role": "user", "content": "I couldn't find a ```lean block. Send the whole file."})
            continue

        PROOF.write_text(candidate)
        ok, guard_out = run_guard()
        print("  " + guard_out.strip().splitlines()[0])
        if ok:
            print(f"\nACCEPTED after {rnd} round(s). Token totals: {totals}")
            return 0

        feedback = guard_out
        if "checker did not accept" in guard_out:
            feedback += "\n\nLean output for Lab.Proof:\n" + lean_errors()
        messages.append({"role": "user",
                         "content": f"The checker rejected that proof.\n```\n{feedback}\n```\n"
                                    "Fix it and send the whole file again."})

    print(f"\nGave up after {args.rounds} rounds. Token totals: {totals}")
    print(f"Last attempt left in {PROOF.relative_to(ROOT)}; original in {backup.relative_to(ROOT)}.")
    return 1


if __name__ == "__main__":
    sys.exit(main())

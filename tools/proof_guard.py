#!/usr/bin/env python3
"""proof_guard: decide whether an (LLM-written) proof can be trusted.

Stage 9 of the course. The article's pipeline trusts exactly three things:
the machine model, the theorem *statement*, and the proof checker. This
script enforces that split for the lab in `Lab/`.

The design rule: **nothing the prover wrote may influence the check**,
except the one file it is supposed to write. So:

  1. SANDBOX       - export the trusted tree (`git archive <base>`, default
                     HEAD) into a fresh temporary directory, and copy in
                     ONLY the candidate `Lab/Proof.lean`. Edits the agent made
                     anywhere else (the library, the spec, guard.json, this
                     script, a lakefile, cached .olean files) don't exist there.
  2. PINS          - the frozen files in the sandbox must match the SHA-256s in
                     `Lab/guard.json` (a tripwire: someone changed the reviewed
                     statement or model without re-reviewing). Frozen files
                     edited in the working tree are reported as well.
  3. HYGIENE       - the candidate may not contain escape hatches: `sorry`,
                     axioms, native code, code that runs at build time, new
                     syntax/macros/elaborators, attributes other than `simp`,
                     or imports outside `Lab.Spec` / `Metal.*`. Checked before
                     anything is built, because building a Lean file runs code.
  4. BUILD         - `lake build Lab.Audit` from scratch in the sandbox (the
                     audit gives fast, readable feedback).
  5. EXTERNAL AUDIT- `tools/AxCheck.lean`, run as a separate program, loads the
                     *compiled* proof and checks (a) `Lab.main`'s type is exactly
                     the constant `Lab.Statement` and (b) it depends only on the
                     three standard axioms, by walking the definitions itself.
                     Being a separate program, it is not parsed with any syntax
                     the proof's imports define, so macros can't steer it.
  6. KERNEL REPLAY - `leanchecker Lab.Proof` re-runs every declaration in the
                     proof module through Lean's kernel.

Usage:
  python3 tools/proof_guard.py                    # check Lab/Proof.lean against HEAD
  python3 tools/proof_guard.py --base origin/main # in CI: a ref the prover can't write
  python3 tools/proof_guard.py --proof path.lean  # check some other candidate file
  python3 tools/proof_guard.py --frozen-only      # CI: only check the pins
  python3 tools/proof_guard.py --freeze           # (human only) re-pin after review

Exit status 0 = ACCEPT, 1 = REJECT.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG_REL = Path("Lab") / "guard.json"
PROOF_REL = Path("Lab") / "Proof.lean"

# Patterns that are never allowed in the candidate proof.
BANNED = [
    (r"\bsorry\b", "`sorry`: an unproved hole"),
    (r"\badmit\b", "`admit`: an unproved hole"),
    (r"(^|\s)axiom\s", "`axiom`: an unproved assumption"),
    (r"\bnative_decide\b", "`native_decide`: trusts compiled code, adds an axiom"),
    (r"\bbv_decide\b", "`bv_decide`: adds a native-code axiom (use bv_omega)"),
    (r"\bofReduceBool\b|\bofReduceNat\b", "native reduction: trusts the compiler"),
    (r"implemented_by|\bextern\b", "`implemented_by`/`extern`: swaps in unchecked code"),
    (r"\bunsafe\b|\bpartial\b|\bopaque\b", "`unsafe`/`partial`/`opaque` definitions"),
    (r"#eval|#exit|\brun_cmd\b|\brun_tac\b|\brun_elab\b|\binitialize\b|\bbuiltin_initialize\b",
     "code that runs at build time"),
    (r"\b(elab|elab_rules|macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|"
     r"declare_syntax_cat|simproc|dsimproc)\b",
     "new syntax, macros or elaborators (keep proofs to the shared library)"),
    (r"set_option\s+(debug|maxRecDepth|maxHeartbeats\s+0|pp|trace)", "debug/unbounded options"),
    (r"\bprelude\b", "`prelude`: replaces the standard library"),
    (r"\bimport\b.*\bLean\b(\s|$)|\bimport\s+Lean\.", "importing the Lean metaprogramming API"),
]
ALLOWED_ATTRS = {"simp", "local simp"}
ALLOWED_IMPORT = re.compile(r"^(Lab\.Spec|Metal(\.[A-Za-z0-9_]+)*)$")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(src: str) -> str:
    """Remove Lean comments (nested /- -/ blocks and -- lines), keeping
    newlines so line numbers stay right. A `sorry` in prose doesn't trip the
    scan; one in code can't hide inside a comment-looking construct."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def check_hygiene(code_text: str, label: str) -> list[str]:
    problems = []
    code = strip_comments(code_text)
    for n, line in enumerate(code.splitlines(), 1):
        m = re.match(r"\s*import\s+(\S+)", line)
        if m and not ALLOWED_IMPORT.match(m.group(1)):
            problems.append(f"{label}:{n}: import `{m.group(1)}` is not allowed")
        for pat, why in BANNED:
            if re.search(pat, line):
                problems.append(f"{label}:{n}: {why}\n      {line.strip()}")
        for attrs in re.findall(r"@\[([^\]]*)\]", line) + re.findall(r"\battribute\s*\[([^\]]*)\]", line):
            for a in (x.strip() for x in attrs.split(",")):
                if a not in ALLOWED_ATTRS:
                    problems.append(f"{label}:{n}: attribute `{a}` is not allowed (only {sorted(ALLOWED_ATTRS)})")
    return problems


def check_pins(tree: Path, cfg: dict, label: str) -> list[str]:
    problems = []
    for rel, want in cfg["frozen"].items():
        p = tree / rel
        if not p.exists():
            problems.append(f"frozen file missing in {label}: {rel}")
        elif sha256(p) != want:
            problems.append(f"frozen file differs from the reviewed version in {label}: {rel}")
    return problems


def run(cmd: list[str], cwd: Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def make_sandbox(base: str) -> Path:
    tmp = Path(tempfile.mkdtemp(prefix="proof_guard_"))
    archive = subprocess.run(["git", "-C", str(ROOT), "archive", "--format=tar", base],
                             capture_output=True)
    if archive.returncode != 0:
        raise SystemExit(f"git archive {base} failed: {archive.stderr.decode().strip()}")
    subprocess.run(["tar", "-x", "-C", str(tmp)], input=archive.stdout, check=True)
    return tmp


def reject(msgs: list[str], header: str) -> int:
    print(f"REJECT ({header}):")
    for m in msgs:
        print("  -", m)
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", default="HEAD", help="git ref of the trusted tree (default HEAD)")
    ap.add_argument("--proof", default=str(ROOT / PROOF_REL), help="candidate proof file")
    ap.add_argument("--freeze", action="store_true", help="re-pin the frozen files (human use only)")
    ap.add_argument("--frozen-only", action="store_true", help="only verify the working tree's pins")
    ap.add_argument("--keep", action="store_true", help="keep the sandbox directory for inspection")
    args = ap.parse_args()
    cfg = json.loads((ROOT / CONFIG_REL).read_text())

    if args.freeze:
        cfg["frozen"] = {rel: sha256(ROOT / rel) for rel in cfg["frozen"]}
        (ROOT / CONFIG_REL).write_text(json.dumps(cfg, indent=2) + "\n")
        print("re-pinned:", ", ".join(cfg["frozen"]))
        return 0

    if args.frozen_only:
        problems = check_pins(ROOT, cfg, "the working tree")
        print("frozen files intact" if not problems else "\n".join(problems))
        return 1 if problems else 0

    # 1. sandbox: the trusted tree + only the candidate proof
    candidate = Path(args.proof).read_text()
    sandbox = make_sandbox(args.base)
    try:
        trusted_cfg = json.loads((sandbox / CONFIG_REL).read_text())
        # 2. pins (in the trusted tree, and a warning-level check of the working tree)
        problems = check_pins(sandbox, trusted_cfg, f"base {args.base}")
        problems += [p + " (you may not edit frozen files)"
                     for p in check_pins(ROOT, trusted_cfg, "the working tree")]
        # 3. hygiene of the candidate
        problems += check_hygiene(candidate, "Lab/Proof.lean")
        if problems:
            return reject(problems, "before building anything")
        (sandbox / PROOF_REL).write_text(candidate)

        # 4. build from scratch
        code, out = run(["lake", "build", "Lab.Audit"], sandbox)
        if code != 0 or "axioms OK" not in out:
            lines = [l for l in out.splitlines() if "error" in l or "REJECTED" in l or "sorry" in l]
            return reject(lines[:20] or ["build failed"], "the proof does not check")

        # 5. external audit, immune to the proof's syntax
        code, out = run(["lake", "env", "lean", "--run", "tools/AxCheck.lean",
                         "Lab.Proof", "Lab.main:Lab.Statement"], sandbox)
        if code != 0:
            return reject(out.strip().splitlines(), "external audit")
        audit_line = out.strip().splitlines()[-1]

        # 6. kernel replay of the proof module
        code, out = run(["lake", "env", "leanchecker", "Lab.Proof"], sandbox)
        if code != 0:
            return reject(out.strip().splitlines()[-10:] or ["leanchecker failed"], "kernel replay")

        print(f"ACCEPT: Lab.main proves the frozen Lab.Statement (trusted tree: {args.base}).")
        print("  ", audit_line)
        print("   kernel replay (leanchecker): OK")
        return 0
    finally:
        if args.keep:
            print("sandbox kept at", sandbox)
        else:
            shutil.rmtree(sandbox, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())

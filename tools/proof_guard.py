#!/usr/bin/env python3
"""proof_guard: decide whether an (LLM-written) proof can be trusted.

Stage 9 of the course. The article's pipeline trusts exactly three things:
the machine model, the theorem *statement*, and the proof checker. This
script enforces that split for the lab in `Lab/`:

  1. FROZEN FILES  - the statement (`Lab/Spec.lean`) and the audit
                     (`Lab/Audit.lean`) must be byte-for-byte what a human
                     reviewed. Their SHA-256s are pinned in `Lab/guard.json`.
  2. PROOF HYGIENE - the editable proof file may not contain escape hatches:
                     `sorry`, new axioms, native code, build-time code
                     execution, new syntax/tactics, or imports from outside
                     the allow-list. (Most of these would also be caught by
                     step 3; checking the source too gives clearer errors,
                     and stops build-time code from running at all.)
  3. THE CHECKER   - `lake build Lab.Audit` must succeed. The audit file
                     checks that `Lab.main` has *exactly* the frozen type and
                     depends only on Lean's three standard axioms.

Usage:
  python3 tools/proof_guard.py            # check
  python3 tools/proof_guard.py --freeze   # (human only) re-pin frozen files after review
  python3 tools/proof_guard.py --frozen-only   # CI: only check the frozen files are intact

Exit status 0 = ACCEPT, 1 = REJECT.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIG = ROOT / "Lab" / "guard.json"

# Patterns that are never allowed in an editable proof file.
BANNED = [
    (r"\bsorry\b", "`sorry`: an unproved hole"),
    (r"\badmit\b", "`admit`: an unproved hole"),
    (r"(^|\s)axiom\s", "`axiom`: an unproved assumption"),
    (r"\bnative_decide\b", "`native_decide`: trusts compiled code, adds an axiom"),
    (r"\bbv_decide\b", "`bv_decide`: adds a native-code axiom (use bv_omega)"),
    (r"\bofReduceBool\b|\bofReduceNat\b", "native reduction: trusts the compiler"),
    (r"implemented_by|@\[\s*extern", "`implemented_by`/`extern`: swaps in unchecked code"),
    (r"\bunsafe\b|\bpartial\b", "`unsafe`/`partial` definitions"),
    (r"#eval|#exit|\brun_cmd\b|\brun_tac\b|\brun_elab\b|\binitialize\b|\bbuiltin_initialize\b",
     "code that runs at build time"),
    (r"\b(elab|elab_rules|macro|macro_rules|syntax|notation|infix|prefix|postfix)\b",
     "new syntax or tactics (keep proofs to the shared library)"),
    (r"set_option\s+(debug|maxRecDepth|maxHeartbeats\s+0)", "debug/unbounded options"),
    (r"\bprelude\b", "`prelude`: replaces the standard library"),
]

ALLOWED_IMPORT = re.compile(r"^(Lab\.Spec|Metal(\.[A-Za-z0-9_]+)*)$")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(src: str) -> str:
    """Remove Lean comments (nested /- -/ blocks and -- lines) so that a
    `sorry` in prose doesn't trip the scan, and one in code can't hide."""
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
                out.append("\n")       # keep line numbers stable
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def check_frozen(cfg) -> list[str]:
    problems = []
    for rel, want in cfg["frozen"].items():
        p = ROOT / rel
        if not p.exists():
            problems.append(f"frozen file missing: {rel}")
        elif sha256(p) != want:
            problems.append(f"frozen file CHANGED: {rel} (the statement is not what was reviewed)")
    return problems


def check_hygiene(cfg) -> list[str]:
    problems = []
    for rel in cfg["editable"]:
        code = strip_comments((ROOT / rel).read_text())
        for n, line in enumerate(code.splitlines(), 1):
            m = re.match(r"\s*import\s+(\S+)", line)
            if m and not ALLOWED_IMPORT.match(m.group(1)):
                problems.append(f"{rel}:{n}: import `{m.group(1)}` is not allowed")
            for pat, why in BANNED:
                if re.search(pat, line):
                    problems.append(f"{rel}:{n}: {why}\n      {line.strip()}")
    return problems


def run_checker(cfg) -> tuple[bool, str]:
    proc = subprocess.run(["lake", "build", cfg["audit_target"]], cwd=ROOT,
                          capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and "axioms OK" in out
    return ok, out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--freeze", action="store_true", help="re-pin the frozen files (human use only)")
    ap.add_argument("--frozen-only", action="store_true", help="only verify the frozen files' hashes")
    args = ap.parse_args()
    cfg = json.loads(CONFIG.read_text())

    if args.freeze:
        cfg["frozen"] = {rel: sha256(ROOT / rel) for rel in cfg["frozen"]}
        CONFIG.write_text(json.dumps(cfg, indent=2) + "\n")
        print("re-pinned:", ", ".join(cfg["frozen"]))
        return 0

    if args.frozen_only:
        problems = check_frozen(cfg)
        print("frozen files intact" if not problems else "\n".join(problems))
        return 1 if problems else 0

    problems = check_frozen(cfg) + check_hygiene(cfg)
    if problems:
        print("REJECT (before building anything):")
        for p in problems:
            print("  -", p)
        return 1

    ok, out = run_checker(cfg)
    if not ok:
        print("REJECT: the checker did not accept the proof.")
        errors = [l for l in out.splitlines() if "error" in l or "REJECTED" in l or "sorry" in l]
        for l in errors[:20]:
            print("  ", l)
        return 1

    print("ACCEPT: Lab.main proves the frozen statement, using only the standard axioms.")
    for l in out.splitlines():
        if "axioms OK" in l:
            print("  ", l.split("info: ")[-1])
    return 0


if __name__ == "__main__":
    sys.exit(main())

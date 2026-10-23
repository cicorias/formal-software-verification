# Setup

You need **Lean 4.35** (the version is pinned in `lean-toolchain`). Rocq is only
for Stage 10; a C compiler only for the `c/` demos.

## Lean (recommended: elan + VS Code)

```sh
# 1. elan, the Lean toolchain manager (like rustup)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source ~/.elan/env      # or open a new shell, so `lean` and `lake` are on your PATH

# 2. clone and build — elan reads lean-toolchain and fetches 4.35 automatically
git clone https://github.com/cicorias/formal-software-verification
cd formal-software-verification
lake build            # lessons + solutions; ~1 minute the first time
```

3. Install **VS Code** and the **lean4** extension (`leanprover.lean4`). Open the
   repo folder (not a single file). Open `Metal/S01_LeanForC.lean`; the
   **infoview** panel on the right shows `#eval` output and, inside proofs, the
   current goal. That panel is where you'll spend your time.

There is **no Mathlib** dependency: everything builds against Lean's core and
standard library, so there's nothing big to download.

### Using mise

After cloning the repo, run `mise trust` followed by `mise run setup`. The
`mise.toml` adds `${ELAN_HOME:-$HOME/.elan}/bin` to PATH, installs elan if missing
using the installer above (non-interactively, without modifying your shell
profile), and runs `lake build`. elan downloads the toolchain pinned in
`lean-toolchain`; the installer does not install a separate default toolchain.

`mise run quickstart` also installs the `leanprover.lean4` extension and opens
the repo in VS Code (requires `code` on PATH). For daily commands, activate mise
in your shell or prefix commands with `mise exec --`, e.g.
`mise exec -- lake build Exercises`.

### Alternative: Nix

```sh
nix profile add nixpkgs#lean4          # or: nix-shell -p lean4
lake build
```
Make sure `lean --version` says 4.35.x; other versions may break proofs (tactic
behaviour changes between releases — that is normal in this world, and why the
toolchain is pinned).

## Daily commands

| Command | What |
|---|---|
| `lake build` | Lessons (`Metal/`) + reference solutions. Must stay error- and `sorry`-free. |
| `lake build Exercises` | Your workspace. Every remaining hole shows as `declaration uses 'sorry'`. |
| `lake build Exercises.S03_Specs` | One stage only. |
| `lake env lean path/to/File.lean` | Check one file outside the build (handy for scratch files). |
| `python3 tools/proof_guard.py` | Stage 9: audit `Lab/Proof.lean`. |
| `make -C c demo` | Stage 3/7: fuzzers vs. the bugs. Needs gcc or clang with ASan. |
| `make -C c asm` | Regenerate the RISC-V assembly (needs clang with the RISC-V target). |
| `make -C rocq` | Stage 10: check the Rocq files. |

## Rocq (Stage 10 only)

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover          # Rocq 9.x with its standard library
make -C rocq
```
With Nix: `nix profile add nixpkgs#rocqPackages.rocq-core nixpkgs#rocqPackages.stdlib`,
then `ROCQPATH=$HOME/.nix-profile/lib/coq/9.1/user-contrib make -C rocq`.
Editor: VS Code with **vsrocq**, or Emacs with Proof General.

## C demos

Any gcc or clang with AddressSanitizer works for `make -C c demo`. For
`make -C c asm` you need clang (it has the RISC-V backend built in on most
distributions). `make -C c libfuzzer` additionally needs the libFuzzer runtime
(`libclang-rt-*-dev` on Debian/Ubuntu).

## Using Claude Code with this repo

The repo has a `CLAUDE.md` (layout, commands, tutoring style) and a project
skill, `fv-prove`, for the Stage 9 lab. Run `claude` in the repo root. Good
uses: "explain this goal", "why is `sym` stuck here", "give me a hint for E6.3
without the answer". The lab is the one place where you hand it the whole job
on purpose.

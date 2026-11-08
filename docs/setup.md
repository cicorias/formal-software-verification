# Setup

You need **Lean 4.35** (the version is pinned in `lean-toolchain`). Rocq is only
for Stage 10; a C compiler only for the `c/` demos.

There are two ways to get set up. Both give you the same commands (`mise tasks`):

| | Native (elan + VS Code) | Dev container (Docker or Codespaces) |
|---|---|---|
| Install | elan, and optionally a C compiler, Python, Rocq | Docker + VS Code's *Dev Containers* extension, or nothing at all with Codespaces |
| Stages 0–9 | ✓ quick | ✓ default config `.devcontainer/devcontainer.json` |
| Stage 10 (Rocq) | install Rocq yourself (opam or Nix, below) | ✓ `.devcontainer/rocq/devcontainer.json` (opt-in) |
| Speed | fastest | about the same on Linux; a little slower on macOS/Windows |
| Good when | you're on Linux or macOS and fine installing elan | you want zero installs, you're on Windows, or you want an agent sandboxed (Stage 9) |

## Native: Lean (elan + VS Code)

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

After cloning the repo, run `mise trust` followed by `mise run 0-setup:build`
(the old name `mise run setup` still works). The `mise.toml` adds
`${ELAN_HOME:-$HOME/.elan}/bin` to PATH, installs elan if missing using the
installer above (non-interactively, without modifying your shell profile), and
runs `lake build`. elan downloads the toolchain pinned in `lean-toolchain`; the
installer does not install a separate default toolchain.

`mise run 0-setup:vscode` (alias `quickstart`) also installs the
`leanprover.lean4` extension and opens the repo in VS Code (requires `code` on
PATH). `mise run` works without activating mise; to call `lake` directly,
activate mise in your shell or prefix with `mise exec --`, e.g.
`mise exec -- lake build Exercises`.

`mise tasks` lists every command in course order. See
[mise tasks](#mise-tasks) below.

### Alternative: Nix

```sh
nix profile add nixpkgs#lean4          # or: nix-shell -p lean4
lake build
```
Make sure `lean --version` says 4.35.x; other versions may break proofs (tactic
behaviour changes between releases — that is normal in this world, and why the
toolchain is pinned).

## Dev container (optional)

The repo ships two dev containers built from one Dockerfile
(`.devcontainer/Dockerfile`, targets `lean` and `rocq`):

- **Lean, the default:** `.devcontainer/devcontainer.json`. Stages 0–9: Lean 4.35
  with the lean4 extension, gcc/clang with ASan, libFuzzer and the RISC-V
  backend, Python 3 + `anthropic`, mise, Claude Code. Builds in a few minutes.
- **Lean + Rocq, opt-in:** `.devcontainer/rocq/devcontainer.json`. Everything
  above plus Rocq 9.1, its stdlib and the vsrocq extension. Pick it when you
  reach Stage 10. The first build also compiles Rocq with opam (a few extra minutes); Docker
  caches it after that.

How to open one:

- **Codespaces:** *Code → Codespaces → Create codespace on main* gives you the
  Lean container. For Rocq: *… → New with options → Dev container
  configuration → "Proofs to the Metal: Lean + Rocq"*.
- **VS Code + Docker:** install the *Dev Containers* extension, then **Dev
  Containers: Reopen in Container** and choose a config. Switch later with **Dev
  Containers: Switch Container**.
- **Terminal:** `mise run 7-container:shell-lean` or `7-container:shell-rocq`
  (uses the devcontainer CLI via `npx`).

On first start, `.devcontainer/post-create.sh` runs `lake build` (and
`make -C rocq` in the Rocq container), so the course is ready when the editor
opens. Give Docker **8 GB of memory or more**: long proofs keep Lean's kernel
busy, and with too little RAM that looks like a hang. Troubleshooting (git
"dubious ownership", CRLF on Windows, the API key, the `.lake` volume):
[.devcontainer/README.md](../.devcontainer/README.md).

## mise tasks

`mise tasks` prints the menu. Names are `<N>-<area>:<action>`; the digit puts
them in the order you'll need them:

| Group | Tasks | Stage |
|---|---|---|
| `0-setup` | `build` (run first), `elan`, `vscode` | native setup only; the dev container comes ready |
| `1-lean` | `build`, `exercises`, `stage <S03_Specs>`, `file <path.lean>` | 1–9 |
| `2-c` | `demo`, `asm`, `libfuzzer` | 3, 5–7 |
| `3-lab` | `guard`, `llm-prove` | 9 |
| `4-rocq` | `check` | 10 |
| `7-container` | `image-lean`, `image-rocq`, `up-lean`, `up-rocq`, `shell-lean`, `shell-rocq` | dev containers |
| `8-ci` | `lean`, `c`, `rocq`, `secrets`, `all` | what GitHub Actions checks |
| `9-clean` | `lean`, `c`, `rocq`, `all` | delete build output |

Arguments go after the task name: `mise run 1-lean:stage S06_NoCrash`,
`mise run 3-lab:llm-prove --rounds 4`.

## Secrets and API keys

**The course needs no secrets.** Lessons, exercises, the C demos, the proof
guard and Rocq all run without any. There is exactly one optional variable:

| Variable | Used by | Needed for | Where to get it |
|---|---|---|---|
| `ANTHROPIC_API_KEY` | `tools/llm_prove.py` (`mise run 3-lab:llm-prove`) | Stage 9's API-loop demo only. **Costs money per run.** | [console.anthropic.com → API keys](https://console.anthropic.com/settings/keys) |

Claude Code (`claude`), the tutor and the `fv-prove` skill, doesn't use this
variable. It has its own login (`claude`, then follow the prompt).

**Where to put it.** Pick one:

- **`.env` file (recommended):** `cp .env.example .env`, then uncomment and fill
  in the line. `.env` is gitignored. `mise.toml` loads it into every `mise run`
  task, natively and in the dev containers (the repo is mounted, so the same
  file works in both), and mise redacts the value in its output.
- **Shell:** `export ANTHROPIC_API_KEY=…`. Needed if you run
  `python3 tools/llm_prove.py` directly rather than through mise.
- **Codespaces:** add a Codespaces secret named `ANTHROPIC_API_KEY`. The dev
  container declares it, so you're offered the chance to set it when you
  create the codespace.
- An `ant auth login` profile also works for `llm_prove.py`.

**Two gotchas:**

- In `.env`, keep a line **commented out** unless it has a real value. `.env`
  takes precedence over your shell and over Codespaces secrets, and a blank
  `ANTHROPIC_API_KEY=` *unsets* the key you set elsewhere.
- With mise activated in your shell, `.env` variables are in every program's
  environment, Claude Code included. Claude Code may then bill to the API key
  instead of your subscription. Anything running in the dev container, including
  an agent, can also read `.env`: keep only keys you're willing to expose there,
  and prefer a key with a low spending limit.

**Keeping them out of git.** `.gitignore` covers `.env` and `.env.*` (except
`.env.example`) and `.claude/settings.local.json`. CI scans every commit with
gitleaks (`secrets` job in `.github/workflows/ci.yml`), and
`mise run 8-ci:secrets` runs the same scan locally over all history plus your
staged and unstaged changes. It doesn't scan your gitignored `.env`, so a real
key there won't trip it. If a key ever does get committed, **revoke it in the
console first**: deleting the file doesn't remove it from history.

## Daily commands

| Command (mise task) | What |
|---|---|
| `lake build` (`1-lean:build`) | Lessons (`Metal/`) + reference solutions. Must stay error- and `sorry`-free. |
| `lake build Exercises` (`1-lean:exercises`) | Your workspace. Every remaining hole shows as `declaration uses 'sorry'`. |
| `lake build Exercises.S03_Specs` (`1-lean:stage S03_Specs`) | One stage only. |
| `lake env lean path/to/File.lean` (`1-lean:file path/to/File.lean`) | Check one file outside the build (handy for scratch files). |
| `python3 tools/proof_guard.py` (`3-lab:guard`) | Stage 9: audit `Lab/Proof.lean`. |
| `make -C c demo` (`2-c:demo`) | Stage 3/7: fuzzers vs. the bugs. Needs gcc or clang with ASan. |
| `make -C c asm` (`2-c:asm`) | Regenerate the RISC-V assembly (needs clang with the RISC-V target). |
| `make -C rocq` (`4-rocq:check`) | Stage 10: check the Rocq files. |

## Rocq (Stage 10 only)

Easiest: open the **Lean + Rocq dev container** (`.devcontainer/rocq/`, see
[Dev container](#dev-container-optional)). It comes with Rocq 9.1, the stdlib and
vsrocq, and `mise run 4-rocq:check` works straight away. To install natively:

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

Both dev containers include Claude Code. When an agent iterates on proofs, it
runs `lake build` on code it wrote, and Lean can run arbitrary programs at build
time (`#eval`, `run_cmd`). The proof guard bans those in the final proof, but
it's a gate on acceptance, not a sandbox for the work along the way. If you
give the agent broad permissions, doing that inside a container keeps it off
your host.

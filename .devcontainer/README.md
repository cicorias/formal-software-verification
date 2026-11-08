# Dev containers

Two ready-made environments for the course. Both are optional: the native setup
in [docs/setup.md](../docs/setup.md) (elan + VS Code) works just as well for the
Lean stages.

| Config | For | Contains | First build |
|---|---|---|---|
| **`devcontainer.json`** (default) | Stages 0–9 | Lean 4 (pinned by `lean-toolchain`), lean4 extension, gcc/clang with ASan + libFuzzer + RISC-V backend, Python 3 + `anthropic`, mise, Claude Code | a few minutes |
| **`rocq/devcontainer.json`** | Stage 10 (and everything before it) | All of the above + Rocq 9.1 + stdlib + vsrocq | a few minutes more (opam builds Rocq); cached after that |

**Start with the default.** Switch to the Rocq one when you reach Stage 10. Both
mount the same repo checkout, so your exercise work comes with you; each keeps
its own `.lake/` build cache.

## Files

```
.devcontainer/
  Dockerfile               one Dockerfile, two targets: `lean` and `rocq` (= lean + Rocq)
  Dockerfile.dockerignore  limits the build context to lean-toolchain
  devcontainer.json        DEFAULT: Lean (target `lean`)
  rocq/devcontainer.json   opt-in: Lean + Rocq (target `rocq`)
  post-create.sh           runs once per container: git safe.directory, volume
                           ownership, `mise trust`, `lake build` (+ `make -C rocq`)
```

## Opening one

**GitHub Codespaces.** *Code → Codespaces → Create codespace on main* uses the
default (Lean). For Rocq: *Code → Codespaces → … → New with options → Dev
container configuration → "Proofs to the Metal: Lean + Rocq"*.

**VS Code, local Docker.** Install the *Dev Containers* extension, open the
repo, run **Dev Containers: Reopen in Container**, and choose the config when
asked. To switch later: **Dev Containers: Switch Container** (or *Rebuild and
Reopen in Container*, then pick the other config).

**Terminal only (devcontainer CLI, via npx).**

```sh
mise run 7-container:shell-lean     # create/start the Lean container, open a shell
mise run 7-container:shell-rocq     # same for Lean + Rocq
mise run 7-container:image-lean     # just check that the image builds (plain docker build)
```

## Inside the container

Everything in `mise tasks` works, in course order:

```sh
mise tasks                          # the menu
mise run 1-lean:exercises           # your remaining sorrys
mise run 2-c:demo                   # fuzzers vs. the bugs
mise run 3-lab:guard                # Stage 9 audit
mise run 4-rocq:check               # Stage 10 (Rocq container only)
```

`post-create.sh` has already run `lake build`. If it failed (see below), re-run
`mise run 1-lean:build`.

## Notes and troubleshooting

- **Memory.** Large machine-state proofs keep Lean's kernel busy, and with too
  little RAM that looks like a hang. Give Docker Desktop **8 GB or more**
  (Settings → Resources). Codespaces gets this from `hostRequirements`.
- **`.lake/` is a Docker volume**, not your host's `.lake/`: fast on macOS and
  Windows, and the host and container never step on each other's build output.
  To start fresh, delete the volume (`docker volume ls | grep fsv-lake`) or run
  `mise run 9-clean:lean`.
- **Claude Code** is installed (`claude`). Log in once; `~/.claude` lives on a
  volume, so the login survives rebuilds. The container keeps build-time Lean
  code the agent writes away from your host, which matters in Stage 9.
- **`ANTHROPIC_API_KEY`** is only for `tools/llm_prove.py` (Stage 9), which
  costs money per run. Nothing else needs a secret. Easiest: `cp .env.example .env`
  on the host or in the container (same mounted file), then uncomment the line;
  `mise run 3-lab:llm-prove` picks it up. In Codespaces you can add it as a
  Codespaces secret instead (you're prompted when you create the codespace). It
  is deliberately not copied in from your host environment: an empty value
  would override a Codespaces secret. Full details:
  [docs/setup.md → Secrets and API keys](../docs/setup.md#secrets-and-api-keys).
- **"dubious ownership" / `git archive` failed.** `post-create.sh` marks the
  workspace as a git `safe.directory`. If you skipped it, run
  `git config --global --add safe.directory "$PWD"`.
- **Guard says frozen files "differ" on Windows.** That's CRLF line endings.
  The repo's `.gitattributes` forces LF, but a checkout made before it existed
  keeps CRLF: run `git rm --cached -r . && git reset --hard` (this discards
  uncommitted changes), or clone again. Cloning into the container's volume
  (*Dev Containers: Clone Repository in Container Volume*) avoids this entirely.
- **Updating Lean.** The toolchain is baked into the image from
  `lean-toolchain`. If that file changes, rebuild the container.

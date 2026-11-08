#!/usr/bin/env bash
# Runs once, after a dev container is created (both the default Lean config and rocq/).
# Safe to re-run by hand:  bash .devcontainer/post-create.sh
set -uo pipefail
cd "$(dirname "$0")/.."

say()  { printf '\n\033[1m== %s\033[0m\n' "$*"; }
warn() { printf '\033[33m!! %s\033[0m\n' "$*"; }

say "Git: trust the mounted workspace"
# The workspace is bind-mounted from the host, so its owner can differ from the
# container user. Git then refuses to work in it ("dubious ownership"), and
# tools/proof_guard.py, which runs `git archive`, fails with a confusing message.
git config --global --add safe.directory "$PWD"

say "Volumes: make .lake/ and ~/.claude writable"
# Docker creates named volumes owned by root.
for d in .lake "$HOME/.claude"; do
  mkdir -p "$d" 2>/dev/null || true
  [ -w "$d" ] || sudo chown "$(id -u):$(id -g)" "$d"
done

say "mise: trust this repo's mise.toml"
mise trust --quiet "$PWD/mise.toml" || warn "mise trust failed; run: mise trust"

say "Toolchain"
lean --version
clang --version | head -1
python3 --version
if command -v rocq >/dev/null; then rocq --version | head -1; fi

say "Build lessons + solutions (mise run 1-lean:build)"
if ! mise run 1-lean:build; then
  warn "lake build failed. If it was killed or stalled, give the container more"
  warn "memory (8 GB+). Re-run: mise run 1-lean:build"
fi

if command -v rocq >/dev/null; then
  say "Check the Rocq files (mise run 4-rocq:check)"
  mise run 4-rocq:check || warn "make -C rocq failed. Re-run: mise run 4-rocq:check"
fi

say "Ready. Start with docs/00-orientation.md; 'mise tasks' lists every command in course order."

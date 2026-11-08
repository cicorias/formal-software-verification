# syntax=docker/dockerfile:1
#
# Proofs to the Metal: dev container image. One Dockerfile, two targets:
#
#   lean  Stages 0-9. Lean 4 (version from lean-toolchain), clang/gcc with ASan,
#         the libFuzzer runtime and the RISC-V backend, Python 3 + anthropic, mise.
#   rocq  Stage 10. Everything in `lean`, plus Rocq 9 + stdlib + vsrocq's language
#         server, built with opam (adds ~2-5 minutes to the first build; after
#         that, Docker caches it).
#
# Used by .devcontainer/devcontainer.json (lean) and .devcontainer/rocq/ (rocq). The build context is the
# repo root, but Dockerfile.dockerignore (next to this file) cuts it down to
# lean-toolchain, so nothing else from the repo is baked into the image.
#
# Build by hand:  docker build -f .devcontainer/Dockerfile --target lean .
#   or:           mise run 7-container:image-lean   (or 7-container:image-rocq)

ARG BASE_IMAGE=mcr.microsoft.com/devcontainers/base:ubuntu-24.04

# ---------------------------------------------------------------------------
FROM ${BASE_IMAGE} AS lean

ARG DEBIAN_FRONTEND=noninteractive
ARG MISE_VERSION=v2026.11.3
ARG ANTHROPIC_SDK="anthropic>=2.1,<3"

# C side (c/Makefile): gcc + clang with ASan, libFuzzer runtime, RISC-V target
# (built into Ubuntu's clang), llvm-objdump for poking at binaries. Python for
# tools/proof_guard.py (stdlib only) and tools/llm_prove.py (anthropic SDK).
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      build-essential clang llvm libclang-rt-dev \
      python3 python3-venv \
      ca-certificates curl git make \
 && rm -rf /var/lib/apt/lists/* \
 && clang -print-targets | grep -q riscv32

# Python packages go in a venv: Ubuntu 24.04 refuses system-wide pip installs (PEP 668).
RUN python3 -m venv /opt/venv \
 && /opt/venv/bin/pip install --no-cache-dir "${ANTHROPIC_SDK}" \
 && chown -R vscode:vscode /opt/venv

# mise, so `mise tasks` / `mise run …` work the same inside and outside the container.
RUN curl -fsSL https://mise.run \
      | MISE_VERSION="${MISE_VERSION}" MISE_INSTALL_PATH=/usr/local/bin/mise sh \
 && mise --version

USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=/home/vscode/.elan/bin:/opt/venv/bin:${PATH}

# elan installs no default toolchain; the one pinned in lean-toolchain is fetched
# now, at image build time, so opening the container doesn't download ~1 GB.
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain none --no-modify-path
COPY --chown=vscode:vscode lean-toolchain /tmp/lean-toolchain
RUN tc="$(cat /tmp/lean-toolchain)" \
 && elan toolchain install "$tc" \
 && elan default "$tc" \
 && lean --version

# ---------------------------------------------------------------------------
FROM lean AS rocq

ARG DEBIAN_FRONTEND=noninteractive
# The course is checked against Rocq 9.1.1 (README, "Status and honesty notes").
ARG ROCQ_VERSION=9.1.1

USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      opam ocaml-nox libgmp-dev pkg-config m4 unzip bubblewrap \
 && rm -rf /var/lib/apt/lists/*

USER vscode
ENV OPAMROOT=/home/vscode/.opam \
    OPAMYES=1 \
    OPAMCONFIRMLEVEL=unsafe-yes \
    OPAMNODEPEXTS=1
# The opam switch uses Ubuntu's OCaml (ocaml-system), so opam doesn't spend time
# compiling a compiler. Sandboxing is off because bubblewrap can't nest inside
# an unprivileged container build.
RUN opam init --bare --disable-sandboxing --no-setup \
 && opam switch create default ocaml-system \
 && opam install --switch=default \
      "rocq-core.${ROCQ_VERSION}" rocq-stdlib vsrocq-language-server \
 && opam clean --all-switches --download-cache --logs --repo-cache
# What `eval $(opam env)` would set, so rocq and vsrocqtop are on PATH everywhere,
# VS Code's extension host included.
ENV OPAM_SWITCH_PREFIX=/home/vscode/.opam/default \
    CAML_LD_LIBRARY_PATH=/home/vscode/.opam/default/lib/stublibs:/usr/lib/ocaml/stublibs \
    PATH=/home/vscode/.opam/default/bin:${PATH}
RUN rocq --version && command -v vsrocqtop

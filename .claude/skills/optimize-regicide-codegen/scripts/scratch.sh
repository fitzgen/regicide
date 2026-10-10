#!/bin/sh
# Make a buildable scratch copy of the worktree for probes and patched builds.
# A `git archive` of `src examples` alone does not build: the crate
# `include_str!`s README.md and visualizer files, and the workspace needs
# fuzz/Cargo.toml. Never copy fuzz/ whole (its corpus is huge).
#   scratch.sh DIR [REV]
set -e
DIR=$1
REV=${2:-HEAD}
SRC=$(git rev-parse --show-toplevel)
rm -rf "$DIR"
mkdir -p "$DIR"
git archive "$REV" | tar -x -C "$DIR"
rm -rf "$DIR/fuzz"
mkdir -p "$DIR/fuzz"
git show "$REV:fuzz/Cargo.toml" > "$DIR/fuzz/Cargo.toml" 2>/dev/null || true
mkdir -p "$DIR/fuzz/fuzz_targets"
git ls-tree --name-only "$REV:fuzz/fuzz_targets" 2>/dev/null | while read -r f; do
    git show "$REV:fuzz/fuzz_targets/$f" > "$DIR/fuzz/fuzz_targets/$f"
done
echo "$DIR ready at $(git rev-parse --short "$REV")"

#!/usr/bin/env bash
# Prove two builds of the `run` example produce byte-identical allocations.
#
#   check_identical.sh BASELINE_RUN CANDIDATE_RUN OUT_DIR PATH...
#
# Runs each build without `-q` over every PATH (corpus directories, input-set
# directories, or single inputs), so the whole allocation -- every operand's
# location and every edit -- is printed, and diffs the two. With --check, the
# candidate's allocations are also verified by regicide's checker.
#
# Exits 0 only when the outputs are identical. On a difference, the diff is in
# OUT_DIR/<n>.diff; the first hunk names the input that changed.
#
# Each PATH is run as its own process, so put the heavy inputs in separate
# PATHs and run several of these at once if you are in a hurry.
set -euo pipefail

check=
if [[ "${1:-}" == "--check" ]]; then
    check=--check
    shift
fi
if [[ $# -lt 4 ]]; then
    sed -n '2,15p' "$0"
    exit 2
fi

base=$1
cand=$2
out=$3
shift 3
mkdir -p "$out"
unset RUST_LOG

status=0
n=0
for path in "$@"; do
    n=$((n + 1))
    "$base" "$path" > "$out/$n.base.txt" 2>&1 || true
    "$cand" $check "$path" > "$out/$n.cand.txt" 2>&1 || true
    if [[ -n "$check" ]] && grep -q 'CHECKER FAILED' "$out/$n.cand.txt"; then
        echo "CHECKER FAILED for $path; see $out/$n.cand.txt"
        status=1
    fi
    # --check adds nothing to the output on success, so the files stay
    # comparable.
    if diff -u "$out/$n.base.txt" "$out/$n.cand.txt" > "$out/$n.diff"; then
        rm "$out/$n.diff" "$out/$n.base.txt" "$out/$n.cand.txt"
        echo "identical: $path"
    else
        echo "DIFFERENT: $path (see $out/$n.diff)"
        status=1
    fi
done
exit $status

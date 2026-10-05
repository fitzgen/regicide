#!/usr/bin/env bash
# Disassemble the functions in a `profiling` build of `run` whose names match a
# pattern, interleaved with the source lines they came from.
#
#   disasm.sh [-l] BINARY PATTERN > out.asm
#
# PATTERN is a `grep -E` over *demangled* names, e.g.
# 'Assignments<u16>>::interference_weight'. Every monomorphization that
# matches is printed, so narrow it to one `<u8>`/`<u16>`/`<u32>` instance --
# the profile says which one is hot. `-l` lists the matching symbols instead.
#
# Needs the binary built with line tables (see SKILL.md, "Build"); a dSYM is
# created beside it on first use, since `objdump --source` on macOS only finds
# line info through one.
set -euo pipefail

list=
if [[ "${1:-}" == "-l" ]]; then
    list=1
    shift
fi
if [[ $# -ne 2 ]]; then
    sed -n '2,13p' "$0"
    exit 2
fi
bin=$1
pattern=$2

dsym="$bin.dSYM/Contents/Resources/DWARF/$(basename "$bin")"
if [[ "$(uname)" == Darwin && ( ! -f "$dsym" || "$bin" -nt "$dsym" ) ]]; then
    dsymutil "$bin" >&2
fi

# Mangled names, paired with their demangled form so the pattern can be
# written against what a human reads in the profile.
syms=$(objdump --syms "$bin" | awk '$3 == "F" || $2 == "F" {print $NF}' | sort -u)
matches=$(paste <(echo "$syms") <(echo "$syms" | rustfilt) | grep -E -- "$pattern" || true)
if [[ -z "$matches" ]]; then
    echo "no function matches: $pattern" >&2
    exit 1
fi
if [[ -n "$list" ]]; then
    echo "$matches" | cut -f2
    exit 0
fi

echo "$matches" | cut -f1 | while read -r sym; do
    if [[ "$(uname)" == Darwin ]]; then
        objdump -d --no-show-raw-insn --source --dsym="$dsym" \
            --disassemble-symbols="$sym" "$bin"
    else
        objdump -d --no-show-raw-insn --source \
            --disassemble-symbols="$sym" "$bin"
    fi
done | rustfilt

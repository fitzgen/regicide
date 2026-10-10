"""Rank two `run` printouts' per-block weighted edit-cost delta.

The delta by loop depth, and the blocks that moved most. Block ids are stable
between two allocations of one input, so they match directly, which is why
this needs no patched build: run `run` on both commits and diff the
printouts.

    python3 block_delta.py BASE.txt CAND.txt
"""

import collections
import os
import sys

# `python3 -I` drops the script's own directory from `sys.path`, and the
# environment asks for `-I` when reading untrusted corpora, so find `loops`
# next to this file rather than relying on the default path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import loops

COST = {"RegReg": 1.0, "Remat": 1.0, "Spill": 5.0, "Reload": 5.0}


def costs(path):
    order, succs, edits, ops = loops.parse(path)
    preds = collections.defaultdict(list)
    for b, ss in succs.items():
        for s in ss:
            preds[s].append(b)
    bodies = {}
    for latch, header in loops.back_edges(order[0], succs):
        bodies.setdefault(header, set()).update(
            loops.natural_loop(latch, header, preds))
    depth = collections.Counter()
    for body in bodies.values():
        for b in body:
            depth[b] += 1
    out = {}
    for b in order:
        w = 10.0 ** depth[b]
        out[b] = (sum(n * COST[k] * w for k, n in edits[b].items()),
                  depth[b], dict(edits[b]))
    return out


def main():
    base, cand = costs(sys.argv[1]), costs(sys.argv[2])
    by_depth = collections.Counter()
    rows = []
    for b in set(base) | set(cand):
        bc, bd, be = base.get(b, (0.0, 0, {}))
        cc, cd, ce = cand.get(b, (0.0, 0, {}))
        d = cc - bc
        if d:
            by_depth[max(bd, cd)] += d
            rows.append((d, b, max(bd, cd), be, ce))
    print(f"total delta {sum(r[0] for r in rows):+,.0f}")
    print("\nby loop depth:")
    for dep in sorted(by_depth):
        print(f"  depth {dep}: {by_depth[dep]:+,.0f}")
    rows.sort()
    print("\nmost improved:")
    for d, b, dep, be, ce in rows[:8]:
        print(f"  block{b} d{dep} {d:+,.0f}: "
              f"{dict(sorted(be.items()))} -> {dict(sorted(ce.items()))}")
    print("\nmost regressed:")
    for d, b, dep, be, ce in rows[::-1][:8]:
        print(f"  block{b} d{dep} {d:+,.0f}: "
              f"{dict(sorted(be.items()))} -> {dict(sorted(ce.items()))}")


if __name__ == "__main__":
    main()

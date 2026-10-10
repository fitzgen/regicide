"""How much of an input's edit cost sits on a loop's entry and exit edges.

Analysis 008's finding #3 (and 007's loop-exit stubs) says the region a loop
owns picks registers for its live-through values independently of its parent,
and the boundary edges pay the difference. This measures that: for each block,
whether it sits on an edge where loop depth changes, and what its edits cost.

    python3 boundary_moves.py PRINTOUT...
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


def classify(path):
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

    buckets = collections.Counter()
    move_buckets = collections.Counter()
    for b in order:
        if not edits[b]:
            continue
        w = 10.0 ** depth[b]
        cost = sum(n * COST[k] * w for k, n in edits[b].items())
        moves = edits[b]["RegReg"] * w
        # Which side of a depth change the block sits on. Test the
        # predecessors' depths, not how many there are: a loop header always
        # has at least two predecessors (a preheader and a latch), so any rule
        # requiring a single one can never fire for a real loop and silently
        # reports every loop entry as interior.
        entry = any(depth[p] < depth[b] for p in preds[b])
        exit_ = any(depth[p] > depth[b] for p in preds[b])
        key = ("entry" if entry else "exit" if exit_ else "interior")
        buckets[key] += cost
        move_buckets[key] += moves
    return buckets, move_buckets


def main():
    total = collections.Counter()
    total_moves = collections.Counter()
    for path in sys.argv[1:]:
        b, m = classify(path)
        total.update(b)
        total_moves.update(m)
        t = sum(b.values())
        name = path.split("/")[-1]
        print(f"{name}: edit cost {t:,.0f}   "
              + "  ".join(f"{k} {v:,.0f} ({100 * v / t:.0f}%)"
                          for k, v in b.most_common()))
    t = sum(total.values())
    tm = sum(total_moves.values())
    print(f"\nTOTAL edit cost {t:,.0f}")
    for k, v in total.most_common():
        print(f"  {k:9} {v:16,.0f}  {100 * v / t:5.1f}%   "
              f"of which moves {total_moves[k]:,.0f} "
              f"({100 * total_moves[k] / tm:.1f}% of all move cost)")


if __name__ == "__main__":
    main()

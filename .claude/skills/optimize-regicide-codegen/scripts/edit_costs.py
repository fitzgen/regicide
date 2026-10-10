"""Weigh one input's edits by kind and loop depth, from a `run` printout.

Loop depth comes from `loops.py`'s natural loops, which match
`Output::loop_depth`. Cold blocks are not distinguished: the printout does not
mark them, and at 0.05x they are a rounding error in these corpora.

    python3 edit_costs.py PRINTOUT [--latches]
"""

import argparse
import collections
import os
import sys

# `python3 -I` drops the script's own directory from `sys.path`, and the
# environment asks for `-I` when reading untrusted corpora, so find `loops`
# next to this file rather than relying on the default path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import loops

COST = {"RegReg": 1.0, "Remat": 1.0, "Spill": 5.0, "Reload": 5.0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("printout")
    ap.add_argument("--latches", action="store_true",
                    help="also sum the edits that sit on loop latches")
    args = ap.parse_args()

    order, succs, edits, operands = loops.parse(args.printout)
    entry = order[0]
    preds = collections.defaultdict(list)
    for b, ss in succs.items():
        for s in ss:
            preds[s].append(b)
    bodies = {}
    for latch, header in loops.back_edges(entry, succs):
        bodies.setdefault(header, set()).update(
            loops.natural_loop(latch, header, preds))
    depth = collections.Counter()
    for body in bodies.values():
        for b in body:
            depth[b] += 1
    latches = {l for l, _ in loops.back_edges(entry, succs)}

    by_kind = collections.Counter()
    by_depth = collections.Counter()
    by_both = collections.Counter()
    latch_cost = collections.Counter()
    for b in order:
        w = 10.0 ** depth[b]
        for kind, n in edits[b].items():
            c = n * COST[kind] * w
            by_kind[kind] += c
            by_depth[depth[b]] += c
            by_both[(depth[b], kind)] += c
            if b in latches:
                latch_cost[kind] += c

    total = sum(by_kind.values())
    print(f"edit cost {total:,.0f} over {len(order)} blocks")
    print("\nby kind:")
    for k, c in by_kind.most_common():
        print(f"  {k:7} {c:14,.0f}  {100 * c / total:5.1f}%")
    print("\nby loop depth:")
    for d in sorted(by_depth):
        print(f"  depth {d} {by_depth[d]:14,.0f}  {100 * by_depth[d] / total:5.1f}%"
              + "   " + "  ".join(f"{k} {by_both[(d, k)]:,.0f}"
                                  for k in COST if by_both[(d, k)]))
    if args.latches:
        lt = sum(latch_cost.values())
        print(f"\non loop latches: {lt:,.0f} ({100 * lt / total:.1f}%)   "
              + "  ".join(f"{k} {v:,.0f}" for k, v in latch_cost.most_common()))


if __name__ == "__main__":
    main()

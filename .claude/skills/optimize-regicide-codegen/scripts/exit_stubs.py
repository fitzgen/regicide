"""Rank loop-exit blocks by the weighted cost of the edits they carry.

Analysis 008's finding #3 says a loop's exit edge pays for the parent region
choosing different locations than the loop did. An exit block here is a block
outside a loop whose predecessors are all inside it, which is the shape of the
stubs that finding quotes.
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


def analyze(path):
    order, succs, edits, operands = loops.parse(path)
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
    return order, succs, preds, edits, operands, bodies, depth


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("printout")
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()
    order, succs, preds, edits, operands, bodies, depth = analyze(args.printout)

    rows = []
    for header, body in bodies.items():
        for b in body:
            for s in succs.get(b, ()):
                if s in body or depth[s] >= depth[b]:
                    continue
                # a stub: every predecessor is in this loop
                if not all(p in body for p in preds[s]):
                    continue
                w = 10.0 ** depth[s]
                cost = sum(n * COST[k] * w for k, n in edits[s].items())
                if cost:
                    rows.append((cost, s, header, depth[s], depth[b],
                                 dict(edits[s]), len(preds[s])))
    rows.sort(reverse=True)
    total = sum(r[0] for r in rows)
    print(f"{len(rows)} loop-exit stubs carrying edits, "
          f"weighted cost {total:,.0f}")
    for cost, s, header, d, bd, e, np in rows[: args.top]:
        print(f"  block{s} (exit of loop block{header}, depth {bd} -> {d}, "
              f"{np} pred): {cost:,.0f}   "
              + "  ".join(f"{k} {v}" for k, v in sorted(e.items())))


if __name__ == "__main__":
    main()

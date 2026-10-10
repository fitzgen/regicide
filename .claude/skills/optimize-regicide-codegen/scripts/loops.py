r"""Find loops, latches and per-block edits in a `run` printout.

    python3 loops.py PRINTOUT [--latch-reloads N]

Blocks are `  block7:` or `  block7(v1, v2) -> (...)` (`entry block0:` for the
entry); successors are `    --> block9` with optional arguments. **A block
header may carry parameters, so the regex has to accept `(` as well as `:`**:
matching only `block(\d+):` finds zero loop headers in any function whose
blocks take parameters, while still parsing most of the blocks.

Loop depth is the natural loops of the back edges found by a DFS over that
graph, which is what regicide's region tree computes too, so these depths
match `Output::loop_depth`.
"""

import argparse
import collections
import re
import sys

BLOCK = re.compile(r"^  (?:entry )?block(\d+)[:(]")
SUCC = re.compile(r"^    --> block(\d+)")
EDIT = re.compile(r"^      edit: (?:Move\((\w+)|(Remat))")
OPERAND = re.compile(r"^      \w+ (?:def|use) ")


def parse(path):
    blocks, succs, edits, operands, order = {}, {}, {}, {}, []
    cur = None
    with open(path) as f:
        for line in f:
            m = BLOCK.match(line)
            if m:
                cur = int(m.group(1))
                order.append(cur)
                blocks[cur] = line.rstrip()
                succs[cur], edits[cur], operands[cur] = [], collections.Counter(), 0
                continue
            if cur is None:
                continue
            m = SUCC.match(line)
            if m:
                succs[cur].append(int(m.group(1)))
                continue
            m = EDIT.match(line)
            if m:
                edits[cur][m.group(1) or m.group(2)] += 1
                continue
            if OPERAND.match(line):
                operands[cur] += 1
    return order, succs, edits, operands


def back_edges(entry, succs):
    """Back edges by DFS: an edge to a block on the current stack."""
    on_stack, seen, edges = set(), set(), []
    stack = [(entry, iter(succs.get(entry, ())))]
    on_stack.add(entry)
    seen.add(entry)
    while stack:
        node, it = stack[-1]
        nxt = next(it, None)
        if nxt is None:
            on_stack.discard(node)
            stack.pop()
            continue
        if nxt in on_stack:
            edges.append((node, nxt))
        elif nxt not in seen:
            seen.add(nxt)
            on_stack.add(nxt)
            stack.append((nxt, iter(succs.get(nxt, ()))))
    return edges


def natural_loop(latch, header, preds):
    """The natural loop of a back edge: header plus everything reaching the
    latch without going through the header.

    The header seeds `body` but never the worklist: it is the barrier that
    stops the backward walk. For a self-loop (`latch == header`) that means
    seeding nothing, since walking back from the header would step straight
    through it and pull in every block that can reach it.
    """
    body, stack = {header}, []
    if latch != header:
        body.add(latch)
        stack.append(latch)
    while stack:
        node = stack.pop()
        for pred in preds.get(node, ()):
            if pred not in body:
                body.add(pred)
                stack.append(pred)
    return body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("printout")
    ap.add_argument("--latch-reloads", type=int, default=0,
                    help="only report latches with at least this many reloads")
    ap.add_argument("--top", type=int, default=20)
    args = ap.parse_args()

    order, succs, edits, operands = parse(args.printout)
    if not order:
        sys.exit("no blocks found")
    entry = order[0]
    preds = collections.defaultdict(list)
    for b, ss in succs.items():
        for s in ss:
            preds[s].append(b)

    loops = {}
    for latch, header in back_edges(entry, succs):
        loops.setdefault(header, set()).update(natural_loop(latch, header, preds))
    latches = {latch: header for latch, header in back_edges(entry, succs)}

    depth = collections.Counter()
    for body in loops.values():
        for b in body:
            depth[b] += 1

    if args.latch_reloads:
        for latch, header in sorted(latches.items()):
            n = edits[latch]["Reload"]
            if n >= args.latch_reloads:
                print(f"latch block{latch} -> block{header} depth {depth[latch]}: "
                      f"{n} reloads, {edits[latch]['RegReg']} moves, "
                      f"{edits[latch]['Spill']} spills")
        return

    print(f"{len(order)} blocks, {len(loops)} loop headers, "
          f"max depth {max(depth.values(), default=0)}")
    for header, body in sorted(loops.items(), key=lambda kv: -depth[kv[0]]):
        print(f"\nloop header block{header}, depth {depth[header]}, "
              f"{len(body)} blocks")
        rows = sorted(body, key=lambda b: -sum(edits[b].values()))[: args.top]
        for b in rows:
            e = edits[b]
            if not sum(e.values()):
                continue
            tag = " LATCH" if b in latches else ""
            print(f"  block{b} depth {depth[b]} ops {operands[b]}{tag}: "
                  + "  ".join(f"{k} {v}" for k, v in sorted(e.items())))


if __name__ == "__main__":
    main()

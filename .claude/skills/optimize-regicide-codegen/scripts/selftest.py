"""Check the printout and event scripts against cases whose answer is known.

    python3 selftest.py

Every one of these guards a bug that shipped: the skill's invariant is that a
measurement script is evidence only once you have tried to break it, and these
are the attempts. Run it after touching any of them.
"""

import collections
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import boundary_moves
import loops

FAILURES = []


def check(name, got, want):
    if got == want:
        print(f"  ok   {name}")
    else:
        print(f"  FAIL {name}: got {got!r}, want {want!r}")
        FAILURES.append(name)


def preds_of(succs):
    preds = collections.defaultdict(list)
    for b, ss in succs.items():
        for s in ss:
            preds[s].append(b)
    return preds


def test_natural_loop():
    """A self-loop is its own body. Seeding the worklist with a latch that is
    the header walks straight back through it and swallows the whole dominator
    chain, which inflated entry-side loop depth tenfold in every consumer."""
    succs = {0: [1], 1: [1, 2], 2: []}
    preds = preds_of(succs)
    check("self-loop back edge", loops.back_edges(0, succs), [(1, 1)])
    check("self-loop body", loops.natural_loop(1, 1, preds), {1})

    # A two-block loop is unaffected, and the entry stays outside it.
    succs = {0: [1], 1: [2], 2: [1, 3], 3: []}
    check("normal loop body", loops.natural_loop(2, 1, preds_of(succs)), {1, 2})

    # A nested loop: the inner body does not reach past the outer header.
    succs = {0: [1], 1: [2], 2: [3], 3: [2, 4], 4: [1, 5], 5: []}
    preds = preds_of(succs)
    check("inner loop body", loops.natural_loop(3, 2, preds), {2, 3})
    check("outer loop body", loops.natural_loop(4, 1, preds), {1, 2, 3, 4})


def test_block_header_regex():
    """A block header may carry parameters. Matching only `blockN:` parses
    most of a function and finds zero loop headers in all of it."""
    check("plain header", bool(loops.BLOCK.match("  block7:")), True)
    check("entry header", bool(loops.BLOCK.match("  entry block0:")), True)
    check(
        "header with params",
        bool(loops.BLOCK.match("  block7(v1, v2) -> (Reg(Reg(r0))):")),
        True,
    )
    check("successor is not a header", bool(loops.BLOCK.match("    --> block9")), None or False)


# A `run` printout with one loop: preheader block0, header block1 (reached
# from the preheader and from the latch, as every real loop header is), body
# block2 which latches back, and exit stub block3. One move in each block, so
# whichever bucket a block lands in is visible in the totals.
SYNTHETIC_PRINTOUT = """=== synthetic ===
Function {
  entry block0:
      edit: Move(RegReg { from: r0, to: r1 })
    inst0
    --> block1

  block1(v0) -> (Reg(Reg(r0))):
      edit: Move(RegReg { from: r0, to: r1 })
    inst1
    --> block2

  block2:
      edit: Move(RegReg { from: r0, to: r1 })
    inst2
    --> block1
    --> block3

  block3:
      edit: Move(RegReg { from: r0, to: r1 })
    inst3
}
"""


def test_boundary_buckets_can_fire(tmp):
    """Every bucket the classifier reports must be reachable. `entry` once was
    not: both its tests wanted a single-predecessor loop header, and a header
    always has at least two (a preheader and a latch), so loop-entry cost was
    silently reported as `interior`.

    This drives `boundary_moves.classify` itself rather than restating its
    rule, so that reintroducing the bug fails the test."""
    path = os.path.join(tmp, "synthetic.txt")
    with open(path, "w") as f:
        f.write(SYNTHETIC_PRINTOUT)

    buckets, _ = boundary_moves.classify(path)
    # block1 is the header, one loop level deep, reached from shallower
    # block0: it is the entry. block3's only predecessor is the deeper
    # block2: it is the exit.
    check("entry bucket fires", buckets.get("entry", 0) > 0, True)
    check("exit bucket fires", buckets.get("exit", 0) > 0, True)
    check("every block is accounted for", sum(buckets.values()), 1 + 10 + 10 + 1)


def test_hint_misses_reads_evictions():
    """Eviction is a third of the ways a bundle gets a register. Ignoring it
    leaves the evictor with no recorded holder and the victim still holding."""
    import hint_misses

    line = ("event: BundleAssignedViaEviction { bundle: bundle12, "
            "alloc: Reg(r3), evicted: bundle9 }")
    m = hint_misses.EV.search(line)
    check("eviction is recognized", bool(m), True)
    if m:
        check("eviction names evictor, reg, victim", m.groups(), ("12", "r3", "9"))


def main():
    tmp = tempfile.mkdtemp(prefix="regicide-selftest-")
    for test in (
        test_natural_loop,
        test_block_header_regex,
        test_boundary_buckets_can_fire,
        test_hint_misses_reads_evictions,
    ):
        print(f"{test.__name__}:")
        if test is test_boundary_buckets_can_fire:
            test(tmp)
        else:
            test()
    print()
    if FAILURES:
        sys.exit(f"{len(FAILURES)} failure(s): {', '.join(FAILURES)}")
    print("all ok")


if __name__ == "__main__":
    main()

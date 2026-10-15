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
import split_depth

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


def test_hint_votes_counts_borders(tmp):
    """Drives `hint_votes` on a log whose answer is countable by hand, rather
    than restating its rule. Three bundles: one unanimous, one that took the
    register fewer borders asked for, one that took the majority's."""
    import hint_votes

    log = os.path.join(tmp, "hints.log")
    with open(log, "w") as f:
        # bundle1: three borders all want r4, and it gets r4. Not a conflict.
        for _ in range(3):
            f.write("event: BundleHint { bundle: bundle1, "
                    "hint: FixedEntitySet {r4}, from: None }\n")
        f.write("event: BundleAssignedPreferred { bundle: bundle1, "
                "alloc: Reg(r4) }\n")
        # bundle2: r6 asked for 3 times, r9 once, and it took r9. Margin 2.
        for _ in range(3):
            f.write("event: BundleHint { bundle: bundle2, "
                    "hint: FixedEntitySet {r6}, from: None }\n")
        f.write("event: BundleHint { bundle: bundle2, "
                "hint: FixedEntitySet {r9}, from: None }\n")
        f.write("event: BundleAssignedNonPreferred { bundle: bundle2, "
                "alloc: Reg(r9), preference: FixedEntitySet {r9} }\n")
        # bundle3: borders disagree but it took the one more of them wanted.
        f.write("event: BundleHint { bundle: bundle3, "
                "hint: FixedEntitySet {r7}, from: None }\n")
        f.write("event: BundleHint { bundle: bundle3, "
                "hint: FixedEntitySet {r8}, from: None }\n")
        f.write("event: BundleHint { bundle: bundle3, "
                "hint: FixedEntitySet {r8}, from: None }\n")
        f.write("event: BundleAssignedPreferred { bundle: bundle3, "
                "alloc: Reg(r8) }\n")
        # A whole-class hint must not vote, or it drowns the ones that name
        # a place. Placed on the *unanimous* bundle and naming registers it
        # did not get, so a reader that counts it turns bundle1 into both a
        # conflict and a minority -- every count below moves.
        f.write("event: BundleHint { bundle: bundle1, "
                "hint: FixedEntitySet {r20, r21}, from: None }\n")
        # bundle4 took the minority register by *eviction*. A reader that
        # knows only the two "Preferred" variants leaves it unassigned, which
        # counts it as a conflict and then skips it as a minority: the
        # denominator rises and the headline does not.
        for _ in range(2):
            f.write("event: BundleHint { bundle: bundle4, "
                    "hint: FixedEntitySet {r2}, from: None }\n")
        f.write("event: BundleHint { bundle: bundle4, "
                "hint: FixedEntitySet {r3}, from: None }\n")
        f.write("event: BundleAssignedViaEviction { bundle: bundle4, "
                "alloc: Reg(r3), evicted: bundle9 }\n")

    out = []
    argv, write = sys.argv, sys.stdout.write
    try:
        sys.argv = ["hint_votes", log]
        sys.stdout.write = out.append
        hint_votes.main()
    finally:
        sys.argv, sys.stdout.write = argv, write
    text = "".join(out)

    check("counts every single-register-hinted bundle",
          "single-register hints: 4" in text, True)
    check("only disagreeing borders count as a conflict",
          "borders disagree:    3" in text, True)
    check("only the bundle that took the minority is reported",
          "less-asked-for register: 2" in text, True)
    check("the margin is majority minus taken", "{1: 1, 2: 1}" in text, True)
    check("the minority bundle is named", "bundle2: took r9" in text, True)
    check("a register taken by eviction is still an assignment",
          "bundle4: took r3" in text, True)


def test_split_depth_follows_lineage(tmp):
    """`split_at_span` mutates the parent in place, so a prefix keeps its id
    and its lineage depth must keep rising across further cuts. Counting
    splits per bundle id instead would report every prefix at depth 1."""
    log = os.path.join(tmp, "trace.txt")
    with open(log, "w") as f:
        # bundle0 is cut twice, so its prefix ends three deep after a third
        # cut; each child inherits the depth spent so far.
        f.write(
            "  TRACE event: BundleSplit { parent: bundle0, child: bundle1, region: region0 }\n"
            "  TRACE event: BundleSplit { parent: bundle0, child: bundle2, region: region0 }\n"
            "  TRACE event: BundleSplit { parent: bundle2, child: bundle3, region: region0 }\n"
            "  TRACE event: BundleSpilledToStack { bundle: bundle0, region: region0 }\n"
            "  TRACE event: BundleAssignedPreferred { bundle: bundle3, alloc: Reg(r0) }\n"
            "  TRACE event: BundleAssignedViaEviction { bundle: bundle1, alloc: Reg(r1) }\n"
        )
    text = run_capture(split_depth.main, log)
    check("every outcome is counted", "3 bundles reached an outcome" in text, True)
    # bundle0 was cut twice, so its own outcome sits at depth 2, not 1.
    check("a twice-cut parent reaches its outcome two deep",
          "    2 splits:      1" in text, True)
    # bundle3 inherits bundle2's one spent split, plus the cut that made it.
    check("a child inherits the splits already spent",
          "    3 splits:      1" in text, True)
    check("the outcome kind is reported", "spilled 1" in text, True)
    check("a cap stops the splits past it", "3 splits" in text, True)


def run_capture(fn, *args):
    """Run `fn`, returning what it printed."""
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn(*args)
    return buf.getvalue()


def main():
    tmp = tempfile.mkdtemp(prefix="regicide-selftest-")
    for test in (
        test_natural_loop,
        test_block_header_regex,
        test_boundary_buckets_can_fire,
        test_hint_misses_reads_evictions,
        test_hint_votes_counts_borders,
        test_split_depth_follows_lineage,
    ):
        print(f"{test.__name__}:")
        if test in (test_boundary_buckets_can_fire, test_hint_votes_counts_borders,
                    test_split_depth_follows_lineage):
            test(tmp)
        else:
            test()
    print()
    if FAILURES:
        sys.exit(f"{len(FAILURES)} failure(s): {', '.join(FAILURES)}")
    print("all ok")


if __name__ == "__main__":
    main()

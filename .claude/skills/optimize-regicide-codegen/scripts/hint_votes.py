"""Tally, per bundle, how many region borders asked for each register, and
what the bundle was assigned.

    RUST_LOG=regicide=trace run -q INPUT 2> LOG
    python3 hint_votes.py LOG

`BundleHint` is logged from `regicide::live_ranges` and the assignments from
`regicide::region_allocation`, so this needs the whole crate's target, not
the `region_allocation` one the other event scripts use.

Reads `BundleHint` events, so it needs no patched build. A bundle whose
borders disagree took a register that *fewer* of them asked for whenever
`RegPreference` broke the tie by arrival order; that count is what found
code-quality-011's kept change (24 of 253 on the raytracer target).

Only single-register hints vote. A wider hint names a class rather than a
place, so counting it would drown the ones that name a register.

**Read the result with the `settled` split in mind.** `hint_across_regions`
emits two kinds of hint and this event does not distinguish them, so a
"minority" here may be a settled hint correctly displacing guesses rather
than a defect. Re-ranking hints *within* one kind was measured flat three
times (code-quality-011 attempts 2, 3 and 5); the distinction that paid was
between kinds.
"""

import collections
import re
import sys

HINT = re.compile(r"BundleHint \{ bundle: bundle(\d+), "
                  r"hint: FixedEntitySet \{([^}]*)\}")
ASSIGNED = re.compile(r"BundleAssigned(?:Non)?Preferred \{ bundle: bundle(\d+), "
                      r"alloc: Reg\((r\d+)\)")
# All three ways a bundle acquires a register count. Miss eviction and the
# evicting bundles -- the high-priority ones, whose hints matter most -- count
# towards `conflicting` but can never reach `minority`, so the headline is a
# biased floor rather than a count.
EVICTED = re.compile(r"BundleAssignedViaEviction \{ bundle: bundle(\d+), "
                     r"alloc: Reg\((r\d+)\)")


def main():
    votes = collections.defaultdict(collections.Counter)
    assigned = {}
    for line in open(sys.argv[1], errors="replace"):
        m = HINT.search(line)
        if m:
            regs = [r.strip() for r in m.group(2).split(",") if r.strip()]
            if len(regs) == 1:
                votes[int(m.group(1))][regs[0]] += 1
            continue
        m = ASSIGNED.search(line) or EVICTED.search(line)
        if m:
            assigned[int(m.group(1))] = m.group(2)

    conflicting = [b for b, v in votes.items() if len(v) > 1]
    minority = []
    for b in conflicting:
        got = assigned.get(b)
        top, top_n = votes[b].most_common(1)[0]
        if got is not None and votes[b][got] < top_n:
            minority.append((top_n - votes[b][got], b, got, top))

    print(f"bundles with single-register hints: {len(votes)}")
    print(f"  of which the borders disagree:    {len(conflicting)}")
    print(f"  assigned a less-asked-for register: {len(minority)}")
    if minority:
        margins = collections.Counter(m[0] for m in minority)
        print("  by margin (majority votes - taken votes):",
              dict(sorted(margins.items())))
        print("  worst:")
        for margin, b, got, top in sorted(minority, reverse=True)[:5]:
            tally = ", ".join(f"{r} x{n}" for r, n in votes[b].most_common())
            print(f"    bundle{b}: took {got}, {top} led by {margin}  ({tally})")


if __name__ == "__main__":
    main()

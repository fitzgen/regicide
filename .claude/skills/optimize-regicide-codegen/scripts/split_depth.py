"""Tally, from a `RUST_LOG=regicide=trace` log, how deep each bundle's split
lineage went and what happened to it in the end.

Fuel semantics: a bundle starts with full fuel; each split spends one, and both
halves inherit what is left. `split_at_span` mutates the parent in place, so the
prefix keeps the parent's id and its fuel keeps falling with every further cut.
"""

import re
import sys
from collections import Counter, defaultdict

SPLIT = re.compile(r"event: BundleSplit \{ parent: (bundle\d+), child: (bundle\d+)")
SPILLED = re.compile(r"event: BundleSpilledToStack \{ bundle: (bundle\d+)")
PREF = re.compile(r"event: BundleAssignedPreferred \{ bundle: (bundle\d+)")
NONPREF = re.compile(r"event: BundleAssignedNonPreferred \{ bundle: (bundle\d+)")
EVICT = re.compile(r"event: BundleAssignedViaEviction \{ bundle: (bundle\d+)")
REMAT = re.compile(r"event: BundleRematerialized \{ bundle: (bundle\d+)")


def main(path):
    # Splits spent on each bundle's lineage so far.
    spent = defaultdict(int)
    outcome = {}
    order = []
    with open(path, errors="replace") as f:
        for line in f:
            if (m := SPLIT.search(line)) is not None:
                parent, child = m.group(1), m.group(2)
                spent[parent] += 1
                spent[child] = spent[parent]
                order.append((parent, spent[parent]))
                continue
            for kind, pat in (
                ("spilled", SPILLED),
                ("preferred", PREF),
                ("non-preferred", NONPREF),
                ("eviction", EVICT),
                ("remat", REMAT),
            ):
                if (m := pat.search(line)) is not None:
                    outcome[m.group(1)] = (kind, spent[m.group(1)])
                    break

    by_depth = Counter(d for _, (_, d) in outcome.items())
    by_depth_kind = defaultdict(Counter)
    for _, (kind, d) in outcome.items():
        by_depth_kind[d][kind] += 1

    total = sum(by_depth.values())
    print(f"{total} bundles reached an outcome; {len(spent)} touched by a split")
    print("\nlineage splits spent -> outcome")
    cum = 0
    for d in sorted(by_depth_kind):
        n = by_depth[d]
        cum += n
        kinds = "  ".join(f"{k} {v}" for k, v in by_depth_kind[d].most_common())
        print(f"  {d:3} splits: {n:6} ({n / total * 100:5.1f}%, cum {cum / total * 100:5.1f}%)  {kinds}")

    # How many splits happen past each fuel level, i.e. what a cap would stop.
    past = Counter()
    for _, d in order:
        past[d] += 1
    print("\nsplits performed at each lineage level (a cap of N stops everything past N)")
    tot_splits = sum(past.values())
    cum = 0
    for d in sorted(past):
        cum += past[d]
        print(f"  split #{d:3}: {past[d]:6}  (cum {cum / tot_splits * 100:5.1f}% of {tot_splits} splits)")


if __name__ == "__main__":
    main(sys.argv[1])

"""Classify, from a `run` event log, why a hinted bundle missed its hint.

    RUST_LOG=regicide::region_allocation=trace run -q INPUT 2> LOG
    python3 hint_misses.py LOG

For each `BundleAssignedNonPreferred` whose allocation is outside its
preference, finds who held the hinted register at that point and whether they
wanted it themselves. A hint lost to a bundle that wanted a *different*
register is one `order_non_preferred_candidates` was supposed to prevent.

All three ways a bundle acquires a register count: preferred, non-preferred
and **via eviction**, which is 8% of acquisitions on a raytracer input. Miss
eviction and two things go wrong at once: a register taken by an evictor has
no recorded holder, so a later miss on it reads as "free (no earlier holder)"
-- the opposite of what happened -- and the bundle it dispossessed stays in
the timeline as though it still held the register.
"""

import collections
import re
import sys

NP = re.compile(r"BundleAssignedNonPreferred \{ bundle: bundle(\d+), "
                r"alloc: Reg\((r\d+)\), preference: FixedEntitySet \{([^}]*)\}")
P = re.compile(r"BundleAssignedPreferred \{ bundle: bundle(\d+), alloc: Reg\((r\d+)\)")
EV = re.compile(r"BundleAssignedViaEviction \{ bundle: bundle(\d+), "
                r"alloc: Reg\((r\d+)\), evicted: bundle(\d+)")


def main():
    events = []
    for line in open(sys.argv[1], errors="replace"):
        m = NP.search(line)
        if m:
            want = {x.strip() for x in m.group(3).split(",") if x.strip()}
            events.append((int(m.group(1)), m.group(2), want, "np", None))
            continue
        m = P.search(line)
        if m:
            events.append((int(m.group(1)), m.group(2), {m.group(2)}, "p", None))
            continue
        m = EV.search(line)
        if m:
            # The evictor's own preference is not in this event; it is whoever
            # holds the register from here on, which is all the timeline needs.
            events.append((int(m.group(1)), m.group(2), set(), "ev",
                           int(m.group(3))))

    # Who holds each register over time. An eviction hands the register over,
    # so the victim stops holding it at that point.
    holders = collections.defaultdict(list)
    for i, (b, r, w, k, evicted) in enumerate(events):
        if evicted is not None:
            holders[r] = [e for e in holders[r] if e[1] != evicted]
        holders[r].append((i, b, k, w))

    why = collections.Counter()
    for i, (b, r, want, kind, _) in enumerate(events):
        if kind != "np" or not want or r in want:
            continue
        for hint in sorted(want):
            earlier = [e for e in holders.get(hint, ()) if e[0] < i]
            if not earlier:
                why["free (no earlier holder)"] += 1
                break
            _, _, ok, ow = earlier[-1]
            if ok == "ev":
                why["holder took it by eviction"] += 1
            elif ok == "p":
                why["holder took it as its own hint"] += 1
            elif ow and hint in ow:
                why["holder hinted at it too"] += 1
            elif ow:
                why["holder had a DIFFERENT hint, took this freely"] += 1
            else:
                why["holder was UNHINTED, took this freely"] += 1
            break

    hinted = sum(1 for _, _, w, _, _ in events if w)
    total = sum(why.values())
    print(f"{len(events)} assignments, {hinted} hinted, {total} missed their hint")
    for k, v in why.most_common():
        print(f"  {v:5}  {100 * v / total:5.1f}%  {k}")


if __name__ == "__main__":
    main()

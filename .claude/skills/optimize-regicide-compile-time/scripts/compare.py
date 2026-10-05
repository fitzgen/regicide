#!/usr/bin/env python3
"""Compare two builds of the `run` example on one input set, with statistics.

Runs the baseline and the candidate alternately (A B A B ..., so slow drift in
host load hits both equally), `-n` rounds each, over the same input set. Each
sample is one process allocating every input in the set, and records:

- `insts`  the sum of the per-input `insts-retired` counts, i.e. instructions
           retired inside `regicide::run` only (decoding and printing are
           excluded);
- `wall`   the process's wall time, which includes decoding the inputs. That
           cost is identical in both builds, so it dilutes the relative delta
           but cannot create one.

For each metric it prints mean, median, min, the relative change of the mean,
a 99% bootstrap confidence interval for that change, and a Mann-Whitney U test
p-value. A change is significant when the CI excludes zero and p < 0.01. The
raw samples go to `--csv`, so they can be pooled or re-analyzed later.

    compare.py -n 20 --csv $R/bench/<slug>-typical.csv \\
        $R/bins/run-<base> $R/bins/run-<cand> $R/sets/typical

Exits 2 if the two builds disagree on any allocation count, which means the
candidate changed the allocator's output; `check_identical.sh` then says where.
"""

import argparse
import math
import os
import random
import re
import statistics
import subprocess
import sys
import time

INSTS = re.compile(r"^  insts-retired (\d+)$", re.M)
COUNTS = re.compile(r"^  (moves \d+ .*slots \d+)$", re.M)


def sample(binary, input_set):
    env = {k: v for k, v in os.environ.items() if k != "RUST_LOG"}
    start = time.perf_counter()
    proc = subprocess.run(
        [binary, "--insts", "-q", input_set], capture_output=True, text=True, env=env
    )
    wall = time.perf_counter() - start
    if proc.returncode != 0:
        sys.exit(f"{binary} failed on {input_set}:\n{proc.stdout[-2000:]}{proc.stderr[-2000:]}")
    # The last `insts-retired` line is the totals block's.
    insts = int(INSTS.findall(proc.stdout)[-1])
    counts = COUNTS.findall(proc.stdout)[-1]
    return insts, wall, counts


def mann_whitney_p(a, b):
    """Two-sided p-value, normal approximation with tie correction."""
    combined = sorted([(x, 0) for x in a] + [(x, 1) for x in b])
    ranks = [0.0] * len(combined)
    i = 0
    ties = 0.0
    while i < len(combined):
        j = i
        while j + 1 < len(combined) and combined[j + 1][0] == combined[i][0]:
            j += 1
        for k in range(i, j + 1):
            ranks[k] = (i + j) / 2 + 1
        t = j - i + 1
        ties += t**3 - t
        i = j + 1
    n1, n2 = len(a), len(b)
    r1 = sum(r for r, (_, g) in zip(ranks, combined) if g == 0)
    u = r1 - n1 * (n1 + 1) / 2
    mu = n1 * n2 / 2
    n = n1 + n2
    sigma = math.sqrt(n1 * n2 / 12 * ((n + 1) - ties / (n * (n - 1))))
    if sigma == 0:
        return 1.0
    z = (abs(u - mu) - 0.5) / sigma
    return math.erfc(max(z, 0) / math.sqrt(2))


def bootstrap_ci(a, b, level=0.99, iters=10000):
    """CI for (mean(b) - mean(a)) / mean(a)."""
    rng = random.Random(0)
    deltas = []
    for _ in range(iters):
        ra = [rng.choice(a) for _ in a]
        rb = [rng.choice(b) for _ in b]
        ma = statistics.fmean(ra)
        deltas.append((statistics.fmean(rb) - ma) / ma)
    deltas.sort()
    lo = deltas[int((1 - level) / 2 * iters)]
    hi = deltas[int((1 + level) / 2 * iters) - 1]
    return lo, hi


def report(name, a, b):
    ma, mb = statistics.fmean(a), statistics.fmean(b)
    delta = (mb - ma) / ma
    lo, hi = bootstrap_ci(a, b)
    p = mann_whitney_p(a, b)
    sig = lo > 0 or hi < 0
    verdict = "SIGNIFICANT" if sig and p < 0.01 else "not significant"
    if sig and p < 0.01:
        verdict += " (faster)" if delta < 0 else " (SLOWER)"
    cv = lambda xs: statistics.stdev(xs) / statistics.fmean(xs) if len(xs) > 1 else 0
    fmt = (lambda x: f"{x:.6g}") if name == "insts" else (lambda x: f"{x:.4f}s")
    print(f"{name}:")
    print(f"  baseline  mean {fmt(ma)}  median {fmt(statistics.median(a))}  "
          f"min {fmt(min(a))}  cv {cv(a):.2%}")
    print(f"  candidate mean {fmt(mb)}  median {fmt(statistics.median(b))}  "
          f"min {fmt(min(b))}  cv {cv(b):.2%}")
    print(f"  delta {delta:+.3%}  99% CI [{lo:+.3%}, {hi:+.3%}]  "
          f"Mann-Whitney p={p:.2g}  => {verdict}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("baseline")
    parser.add_argument("candidate")
    parser.add_argument("input_set", help="directory or single input file")
    parser.add_argument("-n", "--rounds", type=int, default=10)
    parser.add_argument("--csv", help="append raw samples here")
    args = parser.parse_args()

    base_insts, base_wall, cand_insts, cand_wall = [], [], [], []
    base_counts = cand_counts = None
    for i in range(args.rounds):
        # Alternate which goes first, so neither always runs on a warmer host.
        order = [("b", args.baseline), ("c", args.candidate)]
        if i % 2:
            order.reverse()
        for which, binary in order:
            insts, wall, counts = sample(binary, args.input_set)
            if which == "b":
                base_insts.append(insts); base_wall.append(wall); base_counts = counts
            else:
                cand_insts.append(insts); cand_wall.append(wall); cand_counts = counts
            if args.csv:
                new = not os.path.exists(args.csv)
                with open(args.csv, "a") as f:
                    if new:
                        f.write("engine,binary,input_set,round,insts,wall_s\n")
                    f.write(f"{which},{binary},{args.input_set},{i},{insts},{wall:.6f}\n")
        print(f"round {i + 1}/{args.rounds} done", file=sys.stderr)

    print(f"input set: {args.input_set}  rounds: {args.rounds}")
    print(f"baseline:  {args.baseline}")
    print(f"candidate: {args.candidate}")
    report("insts", base_insts, cand_insts)
    report("wall", base_wall, cand_wall)

    if base_counts != cand_counts:
        print(f"\nALLOCATION COUNTS DIFFER -- the candidate changed the output:\n"
              f"  baseline:  {base_counts}\n  candidate: {cand_counts}")
        sys.exit(2)
    print(f"\nallocation counts identical: {base_counts}")


if __name__ == "__main__":
    main()

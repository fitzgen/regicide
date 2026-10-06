#!/usr/bin/env python3
"""Compare two `counts.py` TSVs (baseline, candidate) and gate the candidate.

Every delta is (candidate - baseline) / baseline, so **negative is better**,
the same convention as the codegen-analysis reports.

Inputs are matched by content hash, and only inputs **both** sides finished
with status `ok` are compared; the rest are listed. Summing over inputs that
only one side finished fakes large regressions or wins.

Prints:

1. target and guard functions (from `--targets`), every count;
2. per corpus: estimated cycles, plain counts, and instructions retired;
3. the functions whose estimated cycles moved most, each way, and how many
   got better, worse, or stayed the same;
4. compile-time outliers: inputs whose instructions retired grew by more than
   `--outlier` times and that cost over 1e9 instructions.

Exits 1 when the gate fails, 2 on bad input. The gate fails when:

- any target or guard function's estimated cycles rose;
- any target function lost status `ok` (timed out, failed, checker failed);
- any `--targets` regex matches no input (a typo would silently gate nothing);
- any input that was `ok` in the baseline failed the checker or crashed;
- any corpus's estimated cycles rose by more than `--tolerance` percent;
- the instructions retired summed over typical inputs (baseline cost under
  `--heavy`) rose by more than `--insts-budget` percent;
- any heavy or typical input is a compile-time outlier.

A failed gate is not automatically a dropped attempt; SKILL.md says when a
written justification can override it.

`--targets` is a TSV of `role<TAB>regex<TAB>label`, where `role` is `target`
or `guard` and `regex` is searched for in each input's file name:

    target  tinygo-regex-0188     tinygo countMatches (fix #1)
    guard   hashset-0042          hashset rehash loop (preserve #2)

    diff_counts.py $R/counts/<base>.tsv $R/counts/<cand>.tsv \\
        --targets $R/targets.tsv | tee $R/diffs/<slug>.txt
"""

import argparse
import csv
import re
import sys
from collections import defaultdict

EST = ["est_cycles", "est_reg_operands", "est_stack_operands", "est_moves",
       "est_remats", "est_spills", "est_reloads"]
PLAIN = ["moves", "spills", "reloads", "remats", "slots"]
COLD = ["cold_moves", "cold_spills", "cold_reloads", "cold_remats"]


def load(path):
    with open(path) as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    if rows and "est_cycles" not in rows[0]:
        sys.exit(f"{path}: not a counts.py TSV")
    return {r["sha1"]: r for r in rows}


def num(row, key):
    v = row.get(key, "")
    return float(v) if v else 0.0


def pct(base, cand):
    if base == 0:
        return "+0.00%" if cand == 0 else "new"
    return f"{(cand - base) / base * 100:+.2f}%"


def fmt(x):
    return f"{x:,.0f}" if x == int(x) else f"{x:,.1f}"


def table(header, rows):
    widths = [max(len(str(c)) for c in col) for col in zip(header, *rows)]
    out = ["  ".join(str(c).ljust(w) for c, w in zip(header, widths))]
    out.append("  ".join("-" * w for w in widths))
    out += ["  ".join(str(c).ljust(w) for c, w in zip(r, widths)) for r in rows]
    return "\n".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("baseline")
    parser.add_argument("candidate")
    parser.add_argument("--targets", help="TSV of role, regex, label")
    parser.add_argument("--tolerance", type=float, default=0.5,
                        help="max per-corpus estimated-cycles rise, %% (default 0.5)")
    parser.add_argument("--insts-budget", type=float, default=2.0,
                        help="max typical-set insts rise, %% (default 2)")
    parser.add_argument("--heavy", type=float, default=1e10,
                        help="baseline insts at which an input is heavy (default 1e10)")
    parser.add_argument("--outlier", type=float, default=2.0,
                        help="per-input insts ratio that counts as an outlier (default 2)")
    parser.add_argument("-k", "--top", type=int, default=15)
    args = parser.parse_args()

    base, cand = load(args.baseline), load(args.candidate)
    failures = []

    both = [h for h in base if h in cand
            and base[h]["status"] == "ok" and cand[h]["status"] == "ok"]
    print(f"baseline:  {args.baseline}\ncandidate: {args.candidate}")
    print(f"compared: {len(both)} inputs ok on both sides")

    # Status differences are listed rather than summed.
    status_rows = []
    for h in sorted(set(base) | set(cand), key=lambda h: (base.get(h) or cand[h])["path"]):
        b = base.get(h, {}).get("status", "absent")
        c = cand.get(h, {}).get("status", "absent")
        if b != c:
            name = (base.get(h) or cand[h])["name"]
            status_rows.append((name, b, c))
            if b == "ok" and c in ("checker-failed", "failed"):
                failures.append(f"{name}: {b} -> {c}")
    if status_rows:
        print(f"\n## Status differs ({len(status_rows)}; excluded from every sum)\n")
        print(table(["input", "baseline", "candidate"], status_rows))
    for h in both:
        if cand[h]["status"] == "checker-failed":
            failures.append(f"{cand[h]['name']}: checker failed")

    # 1. Targets and guards.
    if args.targets:
        print("\n## Targets and guards\n")
        rows = []
        with open(args.targets) as f:
            for line in f:
                line = line.rstrip("\n")
                if not line.strip() or line.lstrip().startswith("#"):
                    continue
                role, regex, label = (line.split("\t") + ["", ""])[:3]
                if role not in ("target", "guard"):
                    sys.exit(f"--targets: bad role {role!r} in {line!r}")
                pattern = re.compile(regex)
                matched = [h for h in set(base) | set(cand)
                           if pattern.search((base.get(h) or cand[h])["name"])]
                if not matched:
                    print(f"  (no input matches {role} {regex!r})")
                    failures.append(f"{role} {regex!r} ({label}) matches no input")
                for h in matched:
                    b, c = base.get(h, {}), cand.get(h, {})
                    name = (b or c)["name"]
                    if b.get("status") != "ok" or c.get("status") != "ok":
                        rows.append((role, label, name, b.get("status", "absent"),
                                     c.get("status", "absent"), "", "", "", "", "", ""))
                        if role == "target" and b.get("status") == "ok":
                            failures.append(f"{role} {name}: status {c.get('status')}")
                        continue
                    eb, ec = num(b, "est_cycles"), num(c, "est_cycles")
                    rows.append((
                        role, label, name, fmt(eb), fmt(ec), pct(eb, ec),
                        *(f"{fmt(num(b, k))}->{fmt(num(c, k))}" for k in
                          ["moves", "spills", "reloads", "remats", "slots"]),
                    ))
                    if ec > eb:
                        failures.append(f"{role} {name} ({label}): estimated cycles "
                                        f"{fmt(eb)} -> {fmt(ec)} ({pct(eb, ec)})")
        print(table(["role", "label", "input", "est base", "est cand", "est Δ",
                     "moves", "spills", "reloads", "remats", "slots"], rows))
        # The components say where a change in the total came from.
        print("\nestimated-cycles components (base -> cand):")
        with open(args.targets) as f:
            patterns = [l.split("\t")[1] for l in f
                        if l.strip() and not l.lstrip().startswith("#")]
        for h in both:
            if any(re.search(p, base[h]["name"]) for p in patterns):
                parts = "  ".join(
                    f"{k[4:]} {fmt(num(base[h], k))}->{fmt(num(cand[h], k))}"
                    for k in EST[1:])
                print(f"  {base[h]['name']}: {parts}")

    # 2. Per corpus.
    print("\n## Per corpus\n")
    by_corpus = defaultdict(list)
    for h in both:
        by_corpus[base[h]["corpus"]].append(h)
    rows = []
    for corpus in sorted(by_corpus):
        hs = by_corpus[corpus]
        s = lambda side, k: sum(num(side[h], k) for h in hs)
        eb, ec = s(base, "est_cycles"), s(cand, "est_cycles")
        rows.append((
            corpus, len(hs), fmt(eb), fmt(ec), pct(eb, ec),
            *(pct(s(base, k), s(cand, k)) for k in PLAIN),
            pct(s(base, "cold_moves"), s(cand, "cold_moves")),
            pct(s(base, "insts"), s(cand, "insts")),
        ))
        if eb and (ec - eb) / eb * 100 > args.tolerance:
            failures.append(f"corpus {corpus}: estimated cycles {pct(eb, ec)} "
                            f"> {args.tolerance}%")
    print(table(["corpus", "n", "est base", "est cand", "est Δ", "moves Δ",
                 "spills Δ", "reloads Δ", "remats Δ", "slots Δ", "cold moves Δ",
                 "insts Δ"], rows))

    # 3. Per function.
    deltas = [(num(cand[h], "est_cycles") - num(base[h], "est_cycles"), h) for h in both]
    better = sum(1 for d, _ in deltas if d < 0)
    worse = sum(1 for d, _ in deltas if d > 0)
    print(f"\n## Per function\n\nbetter {better}, worse {worse}, "
          f"unchanged {len(deltas) - better - worse}")
    for title, chosen in [
        ("most regressed", sorted((d for d in deltas if d[0] > 0), reverse=True)),
        ("most improved", sorted(d for d in deltas if d[0] < 0)),
    ]:
        if not chosen:
            continue
        print(f"\n{title}:\n")
        print(table(
            ["input", "corpus", "est base", "est Δ", "est Δ%", "moves", "spills",
             "reloads", "slots"],
            [(base[h]["name"], base[h]["corpus"], fmt(num(base[h], "est_cycles")),
              f"{d:+,.1f}", pct(num(base[h], "est_cycles"), num(cand[h], "est_cycles")),
              *(f"{fmt(num(base[h], k))}->{fmt(num(cand[h], k))}"
                for k in ["moves", "spills", "reloads", "slots"]))
             for d, h in chosen[:args.top]]))

    # 4. Compile time.
    typical = [h for h in both if num(base[h], "insts") < args.heavy]
    tb = sum(num(base[h], "insts") for h in typical)
    tc = sum(num(cand[h], "insts") for h in typical)
    print(f"\n## Compile time (instructions retired in `regicide::run`)\n")
    print(f"typical ({len(typical)} inputs under {args.heavy:.0e}): "
          f"{tb:.4g} -> {tc:.4g} ({pct(tb, tc)})")
    if tb and (tc - tb) / tb * 100 > args.insts_budget:
        failures.append(f"typical insts {pct(tb, tc)} > {args.insts_budget}%")
    outliers = []
    for h in both:
        ib, ic = num(base[h], "insts"), num(cand[h], "insts")
        if ib and max(ib, ic) > 1e9 and ic / ib > args.outlier:
            outliers.append((base[h]["name"], f"{ib:.3g}", f"{ic:.3g}", f"{ic / ib:.2f}x"))
            failures.append(f"compile-time outlier {base[h]['name']}: {ic / ib:.2f}x")
    heavy = [h for h in both if num(base[h], "insts") >= args.heavy]
    for h in sorted(heavy, key=lambda h: -num(base[h], "insts")):
        ib, ic = num(base[h], "insts"), num(cand[h], "insts")
        print(f"heavy {base[h]['name']}: {ib:.4g} -> {ic:.4g} ({pct(ib, ic)})")
    if outliers:
        print("\noutliers:\n")
        print(table(["input", "base insts", "cand insts", "ratio"], outliers))

    print("\n## Gate\n")
    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        sys.exit(1)
    print("pass")


if __name__ == "__main__":
    main()

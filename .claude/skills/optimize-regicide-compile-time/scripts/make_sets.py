#!/usr/bin/env python3
"""Turn a census TSV into the input sets that benchmarking runs over.

Writes, under OUT_DIR:

- `typical/`  every distinct input cheaper than `--heavy` instructions, as
              symlinks. Its summed cost is the "ordinary function" workload,
              where constant factors and data-structure layout dominate.
- `heavy/NN-<name>`  one directory per input at or above `--heavy`, most
              expensive first, each holding a single symlink. These are the
              superlinear cases, where big-O improvements show; each one is
              benchmarked on its own because one of them can cost more than
              all of `typical/` together.
- `sets.md`   what went where, with costs, for the report.

Byte-identical inputs (same sha1, which does happen across corpora) are kept
once. Inputs that failed, were skipped, or timed out in the census are left out
of every set and listed in `sets.md`.

    make_sets.py $R/misc/census.tsv $R/sets
"""

import argparse
import csv
import os
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("census")
    parser.add_argument("out_dir")
    parser.add_argument(
        "--heavy",
        type=float,
        default=1e10,
        help="instructions at which an input becomes `heavy` (default: 1e10)",
    )
    args = parser.parse_args()

    with open(args.census) as f:
        rows = list(csv.DictReader(f, delimiter="\t"))

    seen = set()
    typical, heavy, excluded, dupes = [], [], [], 0
    for row in rows:
        if row["status"] != "ok":
            excluded.append(row)
            continue
        if row["sha1"] in seen:
            dupes += 1
            continue
        seen.add(row["sha1"])
        (heavy if int(row["insts"]) >= args.heavy else typical).append(row)

    if os.path.exists(args.out_dir):
        sys.exit(f"{args.out_dir} already exists; pick a fresh directory")
    os.makedirs(os.path.join(args.out_dir, "typical"))

    for row in typical:
        name = os.path.basename(row["path"])
        os.symlink(row["path"], os.path.join(args.out_dir, "typical", name))

    heavy.sort(key=lambda r: -int(r["insts"]))
    for i, row in enumerate(heavy):
        name = os.path.basename(row["path"])
        d = os.path.join(args.out_dir, "heavy", f"{i:02}-{os.path.splitext(name)[0]}")
        os.makedirs(d)
        os.symlink(row["path"], os.path.join(d, name))

    typical_insts = sum(int(r["insts"]) for r in typical)
    typical_wall = sum(float(r["wall_s"]) for r in typical)
    with open(os.path.join(args.out_dir, "sets.md"), "w") as out:
        out.write(f"# Input sets (from `{args.census}`)\n\n")
        out.write(f"Heavy threshold: {args.heavy:.3g} instructions retired.\n")
        out.write(f"Byte-identical duplicates dropped: {dupes}.\n\n")
        out.write(
            f"## typical/\n\n{len(typical)} inputs, {typical_insts:.4g} insts, "
            f"~{typical_wall:.1f}s summed process wall time.\n\n"
        )
        out.write(f"## heavy/\n\n| dir | insts | wall (s) | bytes |\n| --- | ---: | ---: | ---: |\n")
        for i, row in enumerate(heavy):
            name = os.path.splitext(os.path.basename(row["path"]))[0]
            out.write(
                f"| `{i:02}-{name}` | {int(row['insts']):.4g} | "
                f"{float(row['wall_s']):.1f} | {row['bytes']} |\n"
            )
        if excluded:
            out.write("\n## excluded\n\n")
            for row in excluded:
                out.write(f"- `{row['path']}`: {row['status']}\n")

    print(
        f"typical: {len(typical)} inputs ({typical_insts:.4g} insts); "
        f"heavy: {len(heavy)}; excluded: {len(excluded)}; duplicates: {dupes}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()

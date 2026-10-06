#!/usr/bin/env python3
"""Record what one build of the `run` example allocates for every input.

Runs `run --insts -q [--check] <input>` once per input, in parallel, and writes
one TSV row per input: the allocation counts, the estimated cycles and their
components, instructions retired inside `regicide::run`, process wall time,
and whether the checker passed. `diff_counts.py` compares two such TSVs.

Allocation is deterministic, so one run per build is exact: record the
baseline once, as `$R/counts/<sha>.tsv`, and reuse it for every attempt
measured against that sha.

One process per input, rather than one per corpus, because a corpus's cost is
dominated by a few inputs that take minutes, `run` buffers its stdout, and a
per-input process both parallelizes and says which input is slow.
Instructions retired is a per-process count, so running several at once does
not perturb it; the wall times recorded here *are* perturbed, and are only for
spotting outliers.

Byte-identical inputs (they occur across corpora and across reports) are run
once, under the first path given.

Rows land in `<output>.partial` as each input finishes, and the sorted
`<output>` replaces it at the end.

    counts.py -b $R/bins/run-<sha> -o $R/counts/<sha>.tsv CORPUS_DIR...
    counts.py -b $R/bins/run-<sha> -o $R/counts/<sha>-targets.tsv \\
        --only 'u0-181|countMatches' CORPUS_DIR...
"""

import argparse
import concurrent.futures
import hashlib
import os
import re
import subprocess
import sys
import time

COUNTS = re.compile(
    r"moves (\d+)\s+spills (\d+)\s+reloads (\d+)\s+remats (\d+)\s+"
    r"critical-edges (\d+)\s+slots (\d+)"
)
COLD = re.compile(
    r"of which cold: moves (\d+)\s+spills (\d+)\s+reloads (\d+)\s+remats (\d+)"
)
ESTIMATED = re.compile(
    r"estimated-cycles ([\d.]+)\s+reg-operands ([\d.]+)\s+"
    r"stack-operands ([\d.]+)\s+moves ([\d.]+)\s+remats ([\d.]+)\s+"
    r"spills ([\d.]+)\s+reloads ([\d.]+)"
)
INSTS = re.compile(r"insts-retired (\d+)")

COLUMNS = [
    "corpus", "name", "status", "est_cycles",
    "est_reg_operands", "est_stack_operands", "est_moves", "est_remats",
    "est_spills", "est_reloads",
    "moves", "spills", "reloads", "remats", "critical_edges", "slots",
    "cold_moves", "cold_spills", "cold_reloads", "cold_remats",
    "insts", "wall_s", "sha1", "path",
]


def inputs_in(path):
    if os.path.isfile(path):
        return [path]
    return [
        os.path.join(path, name)
        for name in sorted(os.listdir(path))
        if name.endswith(".postcard") or name.endswith(".json")
    ]


def corpus_label(path):
    """`codegen-analysis-003/corpus-keccak`, so same-named corpora from
    different reports stay apart."""
    parent = os.path.dirname(os.path.abspath(path))
    return f"{os.path.basename(os.path.dirname(parent))}/{os.path.basename(parent)}"


def measure(binary, path, check, timeout):
    cmd = [binary, "--insts", "-q"] + (["--check"] if check else []) + [path]
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env={k: v for k, v in os.environ.items() if k != "RUST_LOG"},
        )
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "wall_s": time.perf_counter() - start}
    row = {"wall_s": time.perf_counter() - start}

    # The per-input block comes before `=== totals`, so the first match of
    # each pattern is this input's.
    out = proc.stdout
    if "skipped:" in out:
        row["status"] = "skipped"
    elif "CHECKER FAILED" in out:
        row["status"] = "checker-failed"
    elif proc.returncode != 0 or "FAILED:" in out or "could not read" in out:
        row["status"] = "failed"
    else:
        row["status"] = "ok"

    for regex, names in [
        (COUNTS, ["moves", "spills", "reloads", "remats", "critical_edges", "slots"]),
        (COLD, ["cold_moves", "cold_spills", "cold_reloads", "cold_remats"]),
        (ESTIMATED, ["est_cycles", "est_reg_operands", "est_stack_operands",
                     "est_moves", "est_remats", "est_spills", "est_reloads"]),
        (INSTS, ["insts"]),
    ]:
        m = regex.search(out)
        if m:
            row.update(zip(names, m.groups()))
    if row["status"] == "ok" and "est_cycles" not in row:
        # A `run` from before estimated cycles existed; refuse rather than
        # record a row that compares as zero.
        row["status"] = "no-estimate"
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("-b", "--binary", required=True, help="the `run` example")
    parser.add_argument("-o", "--output", required=True, help="TSV to write")
    parser.add_argument(
        "-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 2)
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=900,
        help="seconds before giving up on one input (default: 900)",
    )
    parser.add_argument(
        "--no-check",
        action="store_true",
        help="skip the checker (it does not affect insts, which are counted "
        "around `regicide::run` only)",
    )
    parser.add_argument(
        "--only", help="only inputs whose path matches this regex (re.search)"
    )
    parser.add_argument("corpora", nargs="+", help="corpus directories or files")
    args = parser.parse_args()

    paths = []
    for corpus in args.corpora:
        paths.extend(inputs_in(corpus))
    if args.only:
        only = re.compile(args.only)
        paths = [p for p in paths if only.search(p)]

    seen, unique, dupes = set(), [], 0
    for path in paths:
        with open(path, "rb") as f:
            digest = hashlib.sha1(f.read()).hexdigest()[:16]
        if digest in seen:
            dupes += 1
            continue
        seen.add(digest)
        unique.append((path, digest))
    if not unique:
        sys.exit("no inputs found")

    print(
        f"{len(unique)} inputs ({dupes} duplicates dropped), {args.jobs} jobs",
        file=sys.stderr,
    )

    def line(row):
        return "\t".join(str(row.get(c, "")) for c in COLUMNS) + "\n"

    partial = args.output + ".partial"
    rows = []
    with open(partial, "w") as part, concurrent.futures.ThreadPoolExecutor(
        args.jobs
    ) as pool:
        part.write("\t".join(COLUMNS) + "\n")
        futures = {
            pool.submit(measure, args.binary, p, not args.no_check, args.timeout): (p, d)
            for p, d in unique
        }
        for done, future in enumerate(concurrent.futures.as_completed(futures), 1):
            path, digest = futures[future]
            row = future.result()
            row.update(
                corpus=corpus_label(path),
                name=os.path.splitext(os.path.basename(path))[0],
                sha1=digest,
                path=os.path.abspath(path),
                wall_s=f"{row['wall_s']:.3f}",
            )
            rows.append(row)
            part.write(line(row))
            part.flush()
            if row["status"] not in ("ok", "skipped") or float(row["wall_s"]) > 10:
                print(
                    f"[{done}/{len(unique)}] {row['status']} {row['wall_s']}s "
                    f"{row['corpus']}/{row['name']}",
                    file=sys.stderr,
                )
            elif done % 500 == 0:
                print(f"[{done}/{len(unique)}]", file=sys.stderr)

    rows.sort(key=lambda r: (r["corpus"], r["name"]))
    with open(args.output, "w") as out:
        out.write("\t".join(COLUMNS) + "\n")
        for row in rows:
            out.write(line(row))
    os.remove(partial)

    bad = [r for r in rows if r["status"] not in ("ok", "skipped")]
    for r in bad:
        print(f"{r['status']}: {r['path']}", file=sys.stderr)
    print(f"{len(rows)} inputs; {len(bad)} not ok", file=sys.stderr)
    if bad:
        sys.exit(1)


if __name__ == "__main__":
    main()

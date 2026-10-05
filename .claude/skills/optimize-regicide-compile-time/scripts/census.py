#!/usr/bin/env python3
"""Measure what every input in one or more corpora costs to allocate.

Runs `run --insts -q` once per input, in parallel, and writes one TSV row per
input: instructions retired, process wall time, file size, content hash, the
allocation counts, and the path. `make_sets.py` reads this to pick the input
sets that benchmarking uses.

One process per input, rather than one per corpus, for two reasons:

- A corpus's cost is dominated by a handful of inputs that take minutes each,
  and `run` buffers its stdout, so a whole-corpus run tells you nothing about
  which input it is stuck on until it finishes.
- It parallelizes. Instructions retired is a per-process count, so running
  several at once does not perturb it; the wall times recorded here *are*
  perturbed, and are only for ranking.

Duplicate inputs (byte-identical files, which do occur across corpora) are all
recorded; `make_sets.py` drops the duplicates.

Rows land in `<output>.partial` as each input finishes, and the sorted
`<output>` replaces it at the end. `make_sets.py` reads either.

    census.py -b $R/bins/run-<sha> -o $R/misc/census.tsv CORPUS_DIR...
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
INSTS = re.compile(r"insts-retired (\d+)")


def inputs_in(path):
    if os.path.isfile(path):
        return [path]
    found = []
    for name in sorted(os.listdir(path)):
        if name.endswith(".postcard") or name.endswith(".json"):
            found.append(os.path.join(path, name))
    return found


def measure(binary, path, timeout):
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            [binary, "--insts", "-q", path],
            capture_output=True,
            text=True,
            timeout=timeout,
            env={k: v for k, v in os.environ.items() if k != "RUST_LOG"},
        )
    except subprocess.TimeoutExpired:
        return path, "timeout", None, None, time.perf_counter() - start
    wall = time.perf_counter() - start

    # The per-input block comes before `=== totals`; take the first match of
    # each so the totals block is ignored.
    insts = INSTS.search(proc.stdout)
    counts = COUNTS.search(proc.stdout)
    if "skipped:" in proc.stdout:
        status = "skipped"
    elif proc.returncode != 0 or insts is None:
        status = "failed"
    else:
        status = "ok"
    return (
        path,
        status,
        int(insts.group(1)) if insts else None,
        counts.groups() if counts else None,
        wall,
    )


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
        default=3600,
        help="seconds before giving up on one input (default: 3600)",
    )
    parser.add_argument("corpora", nargs="+", help="corpus directories or files")
    args = parser.parse_args()

    paths = []
    for corpus in args.corpora:
        paths.extend(inputs_in(corpus))
    if not paths:
        sys.exit("no inputs found")

    print(f"{len(paths)} inputs, {args.jobs} jobs", file=sys.stderr)

    header = (
        "insts\twall_s\tbytes\tsha1\tstatus\tmoves\tspills\treloads\t"
        "remats\tcritical_edges\tslots\tpath\n"
    )

    def line(row):
        path, status, insts, counts, wall, digest = row
        counts = counts or ("",) * 6
        return (
            f"{insts if insts is not None else ''}\t{wall:.3f}\t"
            f"{os.path.getsize(path)}\t{digest}\t{status}\t"
            + "\t".join(counts)
            + f"\t{os.path.abspath(path)}\n"
        )

    # Rows are appended to `<output>.partial` as they finish, so a census
    # stuck on one slow input still has everything else on disk; the sorted
    # TSV replaces it at the end.
    partial = args.output + ".partial"
    rows = []
    done = 0
    with open(partial, "w") as part, concurrent.futures.ThreadPoolExecutor(
        args.jobs
    ) as pool:
        part.write(header)
        futures = [
            pool.submit(measure, args.binary, p, args.timeout) for p in paths
        ]
        for future in concurrent.futures.as_completed(futures):
            path, status, insts, counts, wall = future.result()
            with open(path, "rb") as f:
                digest = hashlib.sha1(f.read()).hexdigest()[:16]
            row = (path, status, insts, counts, wall, digest)
            rows.append(row)
            part.write(line(row))
            part.flush()
            done += 1
            if status != "ok" or wall > 10:
                print(
                    f"[{done}/{len(paths)}] {status} {wall:.1f}s "
                    f"{insts} {os.path.basename(path)}",
                    file=sys.stderr,
                )
            elif done % 500 == 0:
                print(f"[{done}/{len(paths)}]", file=sys.stderr)

    rows.sort(key=lambda r: -(r[2] or 0))
    with open(args.output, "w") as out:
        out.write(header)
        for row in rows:
            out.write(line(row))
    os.remove(partial)

    total = sum(r[2] or 0 for r in rows)
    bad = [r for r in rows if r[1] not in ("ok", "skipped")]
    print(f"total insts {total:.3e}; {len(bad)} failed or timed out", file=sys.stderr)
    if bad:
        sys.exit(1)


if __name__ == "__main__":
    main()

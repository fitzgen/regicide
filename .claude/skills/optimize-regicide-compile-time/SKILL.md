---
name: optimize-regicide-compile-time
description: >
  Profile and optimize how fast `regicide` runs register allocation (its
  compile time), without changing what it allocates. Use when asked to speed up
  regicide, make register allocation faster, reduce regicide's compile-time
  cost, find what is slow or superlinear in regicide, or recover a regicide
  compile-time regression -- driving the work empirically by replaying
  captured corpora with `examples/run.rs` (`--insts`), the `timing` feature,
  `samply-text`, and disassembly of the hot functions. Produces a series of
  `WIP` commits, one per kept optimization, and a report directory.
---

# Optimize regicide's compile time

Your job is to make `regicide::run` **take less time** on realistic inputs,
**without changing a single allocation decision**, and to leave behind (1) a
series of `WIP` commits that each make it measurably faster and (2) a report of
everything you tried, including what did not work.

No Wasmtime, no Cranelift, no sightglass. The workload is corpora of
already-captured allocator inputs, replayed by `examples/run.rs`.

**Before you start, read `references/known-findings.md`.** It records where
the time goes on the default corpora and the traps earlier sessions fell
into, which together save the first hour. Re-verify anything load-bearing;
regicide changes quickly.

## Invariants

Breaking any of these makes the optimization invalid, however fast it is.

- **Tests pass.** `cargo test --all-features` green, checking cargo's own exit
  code (see "Testing" -- piping through `grep` hides compile failures).
- **Allocation output is byte-identical**, unless the user has explicitly given
  permission to change it *in this session*. `scripts/check_identical.sh` over
  every input set proves it. Different-but-also-valid output is still a
  failure: the user's codegen-quality work is measured against this output.
- **No new `unsafe`**, unless the user explicitly allows it in this session.
- **Statistically significant.** Every kept change has a significant
  improvement on at least one input set and no significant regression on any.
  "It should be faster" is not evidence. See "Measuring".
- **One optimization per `WIP` commit**, and **failed attempts are also
  committed**, so they have a sha for the report, and then dropped from the
  branch (see "Git").
- **Write the report as you go.** After every attempt, before starting the
  next. A reboot must cost at most the attempt in flight.
- Match the surrounding code's style; load the `writing-code-comments` skill
  before writing comments.

## Inputs

- **Corpora.** If the user names some, use those. Otherwise use the corpora
  of the **highest-numbered** `~/regalloc2/reports/codegen-analysis-NNN/`
  directory: every `corpus*` subdirectory of it that is non-empty. Check
  `find <dir> -type f | wc -l`, because one such directory has been seen
  empty. Never write into those directories; they belong to another workflow.
- **Scope** (optional). One pass or file to concentrate on. Without one,
  profile first and let the data choose.
- **Time budget** (optional). Without one, keep going until the profile has no
  hot spot left that you have a credible idea for, then write up.

## Layout of the report directory

```bash
cd <repo root>                      # this worktree; never `cd` elsewhere
ls reports/                         # find the highest compilation-speedup-NNN
R=reports/compilation-speedup-001   # next unused number; set in every shell
mkdir -p $R/{successful,unsuccessful,profiles,misc,bins,bench,sets}
```

`reports/` is gitignored (by `~/.gitignore`), so nothing in it is committed.

| Path | Holds |
| --- | --- |
| `report.md` | Status, baseline, table of every attempt, cumulative result. Created first, updated after every step. Template in `references/report-templates.md`. |
| `successful/<slug>.md` | One per kept optimization: commit sha, what and why, measurements, links into `profiles/` and `bench/`. |
| `unsuccessful/<slug>.md` | One per dropped attempt: commit sha (it stays reachable from the tag, see "Git"), what, why it failed, measurements. |
| `profiles/` | Raw `samply` profiles (`.json.gz`), the `samply-text` reports made from them, timing logs, disassembly. |
| `misc/` | Environment and host load, the census, tool gotchas, and **suggested additions to this skill** (`misc/skill-learnings.md`). |
| `bins/` | A copy of the `run` binary for each commit measured, named `run-<sha>` (and `run-<sha>-prof` for profiling builds). Comparisons need two binaries side by side. |
| `bench/` | Raw per-sample CSVs from `scripts/compare.py`, so any verdict can be re-checked. |
| `sets/` | The input sets (symlinks) from `scripts/make_sets.py`. |

Put the date and time (`date '+%Y-%m-%d %H:%M'`) at the top of every file you
write, and the commit sha every measurement was taken at.

## 0. Setup

1. Create `$R` and a skeleton `report.md` (status: "setting up").
2. **Record the environment** into `$R/misc/environment.md`: `date`,
   `git rev-parse HEAD`, `git status --short`, `rustc -V`, `sysctl -n
   machdep.cpu.brand_string hw.ncpu`, `uptime`, and the top of
   `ps -Ao %cpu,etime,comm -r | head -15`. **Load matters.** This host
   normally runs CrashPlan, Defender, and other agents that use whole cores,
   and other Claude sessions may be fuzzing or benchmarking. Write down what
   was running. Re-check before every benchmark and record it with the result.
3. **Branch.** Work on a fresh branch off the current `HEAD`, e.g.
   `git switch -c compile-speedups-NNN`. Note the base sha in `report.md`.
4. **Baseline tests.** Run the test suite on the untouched tree (see
   "Testing") and record the result. Then a red test later is yours. For
   pre-existing failures, also check the user's memory notes.

## 1. Build

Two builds of the same `run` example, and **both** are copied into `$R/bins/`
after every commit, because `target/` is overwritten by the next build:

```bash
sha=$(git rev-parse --short HEAD)

# Measuring: plain release.
cargo build --release --example run
cp target/release/examples/run $R/bins/run-$sha

# Profiling and disassembly: release plus line tables. Defined with --config
# so Cargo.toml need not change.
cargo build --example run --profile profiling \
    --config 'profile.profiling.inherits="release"' \
    --config 'profile.profiling.debug="line-tables-only"'
cp target/profiling/examples/run $R/bins/run-$sha-prof
```

Do **not** add `split-debuginfo="packed"` to that. It fails on this host with
"Operation not permitted" and leaves stray object files that `dsymutil` then
warns about forever.

What the `run` example builds. This matters when interpreting numbers:

- `examples/run.rs` links regicide with its **dev-dependency features**:
  `checker`, `deserialize`, `entity-repr-8`, `entity-repr-16`, `serialize`,
  `std`, `timing`, `trace-log`, `visualizer`. Production (regalloc2) uses
  `hashbrown`, `entity-repr-8`, and `entity-repr-16` only, with no `std`.
- **`visualizer` makes every `event!` push onto an in-memory log** whose
  events are built eagerly, and `trace-log` evaluates the `trace!` guard. So
  the `run` binary pays for event construction that production does not. On
  one measured input, removing `visualizer`/`trace-log`/`timing` saved only
  ~0.3% of instructions, so it is small but not zero. **An optimization that
  only speeds up event construction is not a production win**: say so in its
  write-up, and do not count it as one.
- `std` swaps `hashbrown::HashMap` for `std::collections::HashMap` (both with
  `FxBuildHasher`, and the same SwissTable underneath). Close enough, but do
  not tune hashing details off the back of it.
- `insts-retired` (see below) is counted around `regicide::run` only, so
  deserializing the input is excluded. Process wall time is not.

## 2. Census and input sets

The corpora are wildly uneven, and that drives the whole method. Measured on
`codegen-analysis-002`'s six corpora at `e53b573`:

- **Most inputs cost 10⁶–10⁹ instructions. A few dozen cost 10¹¹–10¹³.**
  The most expensive, `tinygo-regex-0188` (1.1·10¹³ insts, ~15 minutes) and
  `sqlite3-0226` (5.2·10¹², ~8 minutes), each cost more than everything else
  in their corpus put together. Something in
  regicide is badly superlinear on these.
- Replaying a whole corpus in one process takes **tens of minutes to hours**.
  Before running the census, a naive `run --insts -q <corpus>` looks
  identical to a hang.
- Byte-identical inputs occur across corpora (`shootout-sieve-0061` ==
  `shootout-switch-0063`).

So first measure each input once, then split the corpora into sets:

```bash
S=.claude/skills/optimize-regicide-compile-time/scripts
python3 $S/census.py -b $R/bins/run-$sha -o $R/misc/census.tsv \
    <corpus dir>... 2> $R/misc/census.log           # run in the background
python3 $S/make_sets.py $R/misc/census.tsv $R/sets   # writes $R/sets/sets.md
```

The census runs one process per input, in parallel (`-j`, default ncpu-2),
and records insts, wall time, size, hash, and allocation counts. It takes
over 20 minutes on the default corpora, bounded below by the single slowest
input (~15 minutes for `tinygo-regex-0188`). **Start it in the background
right after the first build, and profile while it runs.** Copy the
heavy-input list from `sets/sets.md` into `report.md`.

The sets:

- **`sets/typical/`** holds every distinct input under 10¹⁰ instructions.
  This is ordinary functions, where constant factors, data layout, and
  allocation churn dominate. It is benchmarked as one process per sample.
- **`sets/heavy/NN-*/`** holds each superlinear input on its own. This is
  where big-O wins show. Benchmark a few individually, never all of them:
  a single `heavy/00` sample can take 15 minutes. Pick 2–3 that run in
  seconds to a minute and profile like the code you are changing. Measure
  `heavy/00` only for the cumulative result, at low `-n`.

Report results **per set**, never as one corpus-wide sum. A sum is dominated
by the heaviest inputs and hides everything that happens to ordinary functions, as
well as anything that regresses them.

Each set also must still pass, unchanged, through `check_identical.sh`
(the "Correctness gate" below).

## 3. Profile

Profile both a heavy input and `typical/`. They usually have different hot
spots, and that is a finding worth recording.

### Which pass: the `timing` feature

Already enabled in the `run` build. Every pass is wrapped in a
`timing::Timing` guard that logs at trace level under the `regicide::timing`
target:

```bash
RUST_LOG=regicide::timing=trace $R/bins/run-$sha -q <input> 2> $R/profiles/timing-<name>.log
```

Each pass prints `Finish timing: <pass>: <N.NNN>ms`, in milliseconds. To
total the passes over a set:

```bash
RUST_LOG=regicide::timing=trace $R/bins/run-$sha -q $R/sets/typical 2>&1 >/dev/null \
    | sed -n 's/.*Finish timing: \(.*\): \([0-9.]*\)ms/\1\t\2/p' \
    | awk -F'\t' '{t[$1]+=$2} END {for (p in t) printf "%10.1f ms  %s\n", t[p], p}' \
    | sort -rn
```

The passes are reverse post-order, region tree, liveness, live ranges,
coalesce, region allocate, place spills, allocate spill slots, generate moves,
output, eliminate redundant moves, and eliminate dead moves. Do not use `RUST_LOG=regicide=trace`
on a heavy input: the full trace log runs for minutes and fills the disk.

The guard measures wall time with `Instant`, so a pass on a sub-millisecond
input is dominated by noise. Sum it over many inputs, or use it on heavy
inputs, and use `--insts` for the comparisons that decide.

### Which functions: `samply-text`

```bash
samply record -s -o $R/profiles/<name>.json.gz -- \
    $R/bins/run-$sha-prof -q <input-or-set>
samply-text report -t -s 1 -n 80 $R/profiles/<name>.json.gz \
    > $R/profiles/<name>-tree.txt
samply-text report -n 60 $R/profiles/<name>.json.gz \
    > $R/profiles/<name>-flat.txt
```

- Use **`samply record -s -o`** directly rather than `samply-text record`.
  The latter deletes its profile afterwards, and the raw profile is what the
  report needs to keep.
- Read the **tree** (`-t`) first, because the flat view's self-time splits
  inlined BTree internals into dozens of rows. Add `-c` if you meet
  recursion.
- A single typical input finishes in milliseconds, which gives too few
  samples. Profile a whole set, or a directory of symlinks to one input
  repeated 40 times (`ln -s`). One heavy input is plenty on its own.
- The generic parameter in a symbol (`<u8>`, `<u16>`, `<u32>`) says which
  entity representation ran (see `run_dispatch` in `src/lib.rs`). The same
  function shows up three times; add them together.

### Why it is hot: disassembly

Look at the machine code of anything above a few percent self time:

```bash
$S/disasm.sh -l $R/bins/run-$sha-prof '<demangled pattern>'   # list matches
$S/disasm.sh $R/bins/run-$sha-prof \
    'Assignments<u16>>::interference_weight' > $R/profiles/<fn>.asm
```

It interleaves source lines (via a `dsymutil` dSYM, created on first use).
Look for:

- **bounds checks** (`cmp`/`b.hs` to a panic) inside the hot loop that an
  iterator, a re-sliced loop, or a hoisted length assert (no `unsafe`)
  could remove;
- **calls that should have inlined**: `bl` to tiny helpers, `memcpy` for
  small structs, and `__rust_alloc`/`__rust_dealloc` inside loops
  (allocation churn);
- **wide loads, stores, and stack spills** of large structs or enums: a hint
  that a type is bigger than it needs to be;
- **pointer chasing**: chains of dependent `ldr`s, typical of `BTreeMap`
  traversal, `Vec<Vec<_>>`, and linked structures;
- **division or modulo** in a hot loop, and repeated recomputation of
  something loop-invariant.

`samply` attributes samples to addresses. When one source line dominates,
it is worth finding which instructions under it are hot. Note that macOS has
no `perf annotate`. The tree report plus the asm is usually enough.

### How often: counters

For "how many times does this loop run, how long is this list typically",
add a temporary `static COUNT: AtomicU64` (or a histogram) and print it at
exit, in an uncommitted edit, then remove it. Write what you learned in
`misc/`. A distribution (for example "92% of calls see ≤4 elements") is what
justifies a fast path.

## 4. Choose what to try

Rank candidates by **estimated saving × breadth**. A 30% speedup of a pass
that is 2% of `typical/` is worth less than 5% of a pass that is 40% of it.
Record each candidate, its estimate, and the profile evidence in `report.md`'s
backlog before starting on it.

Kinds of optimization, roughly in order of how often they pay off here:

- **Better big-O.** Superlinear inputs exist (see "Census and input sets").
  Find the loop nest that grows with function size, with a counter, and
  break it: an index instead of a scan, an interval structure instead of
  repeated range searches, incremental update instead of recomputation.
- **Don't recompute.** Does a later pass rebuild something an earlier pass
  already had (liveness, RPO, block-to-region maps, use lists)? Could it be
  kept in the `Context` and reused?
- **Fast path for the common case.** Measure the distribution. If most calls
  see one element, one region, or no conflicts, handle that inline and leave
  the general case to a cold path (`#[cold]`, `#[inline(never)]`).
- **Data structures.** Replace a `BTreeMap` with a sorted `Vec` and binary
  search when it is built once and read many times, or a hash map with an
  entity-indexed `SecondaryMap` when keys are dense, or a `Vec<Vec<_>>` with
  one flat vector plus offsets.
- **Layout and size.** Shrink hot types: bit-pack flags, use narrower indices
  (the `EntityRepr` machinery exists for this), use `Option<NonZero…>`, and
  reorder fields. Check sizes with a temporary
  `const _: () = assert!(size_of::<T>() == N);`.
- **Split or group by access pattern.** Which fields of a `PrimaryMap<K, V>`
  are read together in the hot loop? Keep those together in `V` and move
  the cold ones into a `SecondaryMap<K, V2>`. Fields always read together
  belong in one `SecondaryMap<K, (A, B)>`, not two maps.
- **Allocation churn.** Reuse buffers kept in the `Context` (it is reset
  between functions, not rebuilt, so cleared vectors keep their capacity),
  avoid `collect()` into a temporary that is immediately iterated, and use
  `SmallVec`-style inline storage only if a dependency is acceptable (ask
  first).
- **Codegen-level.** Remove bounds checks via iterator restructuring, add
  `#[inline]` on cross-module tiny functions, and hoist invariant loads.

Things that are **out of bounds**: changing heuristics, priorities, tie-breaks,
iteration order that can affect a decision, or anything else that changes the
output. Check especially **iteration order of hash maps and sets**: swapping
a `BTreeMap` for a hash map, or changing a hasher, can silently change
decisions that depend on iteration order. `check_identical.sh` catches it,
but think about it first.

## 5. The loop: one attempt

For each candidate:

1. **Re-read the code you are about to change.** Files in this repo get
   edited mid-session by the user and other agents.
2. **Implement it.** Keep it minimal and self-contained, one idea per
   attempt. Then `cargo fmt`.
3. **Correctness gate.** See "Testing" and "Correctness gate" below. A
   failure here ends the attempt: it is unsuccessful, whatever its speed.
4. **Commit** as `WIP: <one line on what it does>` (see "Git").
5. **Build both binaries and copy them into `bins/`** (see "Build").
6. **Measure** against the previous kept commit (see "Measuring").
7. **Decide** using the rule below.
   - **Kept**: write `successful/<slug>.md` and update `report.md`. The next
     attempt's baseline is this commit.
   - **Dropped**: write `unsuccessful/<slug>.md` with the sha, tag it so it
     stays reachable (`git tag regicide-speedup-NNN/<slug> HEAD`), then
     `git reset --hard HEAD^`. Update `report.md`.
8. Re-profile when the profile has plausibly changed, for example after a
   kept win of a few percent or more. The next hot spot is often not the
   one you expected.

Every few kept commits, and always at the end, also measure **the original
base against the current tip** on every set. This gives the cumulative
number, and catches individually-insignificant regressions that add up.

## Testing

```bash
cargo test --all-features > $R/misc/test-<sha>.txt 2>&1; echo "exit=$?"
grep -E '^test result|FAILED|panicked' $R/misc/test-<sha>.txt
```

Check `exit=`, not the grep. When the test build fails to compile there are
no `test result` lines at all, and an empty grep looks like a pass. regicide
has `cfg(test)` struct literals that only the test build sees, so adding a
field to a struct can break tests while `cargo build` stays happy. At
`e53b573` the clean baseline was 389 + 8 passed, 10 ignored, about 2 minutes.

If the change touches anything the fuzzer exercises (most of the allocator),
also run the `allocate` fuzz target. The user's notes require `-s none`,
libFuzzer flags after `--`, and enough `-max_total_time` to get past corpus
loading (roughly 410 s). Run it in the background while you measure:

```bash
cargo +nightly fuzz run -s none allocate -- -max_total_time=700 \
    > $R/misc/fuzz-<sha>.log 2>&1; echo "exit=$?"
grep -E 'INITED|DONE|Done [0-9]+ runs|ERROR|panicked' $R/misc/fuzz-<sha>.log
```

Require `INITED` and `Done` before calling it clean.

## Correctness gate

```bash
$S/check_identical.sh --check $R/bins/run-<base> $R/bins/run-<cand> \
    $R/misc/identical-<sha> $R/sets/typical $R/sets/heavy/<the ones you bench>
```

It prints the full allocation of every input from both builds, diffs them,
and runs the checker on the candidate's. Every path must come out
`identical:`. Per attempt, gate on `typical/` plus the heavy inputs you are
benchmarking: the heaviest take 10+ minutes per build, so the full
`heavy/*` sweep belongs **before the final report** (and every few kept
commits), against the base, in the background. Start the gate as soon as
the build is done and measure instructions while it runs. **Do not record a
verdict until it is clean.** On a difference, the first hunk of the `.diff`
names the input. The attempt changed the output, so it is unsuccessful
unless the user explicitly allowed output changes.

`compare.py` also exits 2 when the per-set totals of the allocation counts
differ, which is a cheap early warning but not a substitute for the gate.

## Measuring

**Wall time is what matters. Instructions retired is the quiet proxy.**

`examples/run.rs --insts` counts instructions retired inside `regicide::run`
for each input (macOS: `proc_pid_rusage`; Linux: `perf_event`). Its noise is
~0.1% CV on this host, against ~5–25% for wall time on small sets, so it
resolves effects of a fraction of a percent with ten samples.

It is **blind to micro-architectural effects**: cache misses, branch
mispredictions, memory-level parallelism, and store forwarding. For a
change whose whole point is locality (shrinking a type, splitting hot from
cold fields, `Vec` instead of `BTreeMap`), a flat instruction count means
"no information", not "no effect". Such changes must be judged on wall time,
with enough samples to resolve it.

```bash
python3 $S/compare.py -n 20 --csv $R/bench/<slug>-typical.csv \
    $R/bins/run-<base> $R/bins/run-<cand> $R/sets/typical \
    | tee $R/bench/<slug>-typical.txt
python3 $S/compare.py -n 10 --csv $R/bench/<slug>-heavyNN.csv \
    $R/bins/run-<base> $R/bins/run-<cand> $R/sets/heavy/NN-* \
    | tee $R/bench/<slug>-heavyNN.txt
```

`compare.py` interleaves the two builds (ABAB, alternating which goes first),
then prints for `insts` and `wall`: mean, median, min, CV, the relative change
of the mean, a 99% bootstrap CI for it, and a Mann–Whitney p-value. It calls
a result significant only when the CI excludes zero **and** p < 0.01. Raw
samples are appended to the CSV, so a second run with `--csv` to the same file
can be pooled by re-running the analysis.

Before trusting any comparison on a new host or set, **run it A-vs-A** (the
same binary twice) and check that it comes out not significant. This was
verified at `e53b573` on `corpus-keccak`: insts +0.06%, CI [−0.13%, +0.23%],
not significant.

### Wall time needs a quiet host

- Run `uptime` and check `ps` first. Do not run `compare.py` alongside your
  own census, the correctness gate, the fuzzer, or a build: they share cores
  and the memory bus. Run the correctness gate during `insts`-only screening
  if you must, but **not** during the wall-time run that decides.
- The `typical/` wall time includes decoding every input, a constant cost
  shared by both builds that dilutes the relative delta. Interpret the
  decision on `insts`, and the magnitude on both.
- If wall time does not resolve, raise `-n` (20 → 50 → 100) before
  concluding anything. Heavy inputs resolve on wall time much more easily,
  since a single sample is seconds to minutes.

### Decision rule

Per set, then across sets:

| insts | wall | verdict |
| --- | --- | --- |
| significant improvement | significant improvement | **keep** |
| significant improvement | not significant | **keep** (record that wall did not resolve, and at what `-n`) |
| significant improvement | significant regression | **drop**, wall wins |
| not significant | significant improvement | **keep** if it is a locality-type change and survives a repeat run at higher `-n`; otherwise suspect noise and repeat |
| not significant | not significant | **drop**: no measured effect, not worth the churn. If it is promising, first raise `-n` once |
| any | significant regression on **any** set | **drop**, or rework so it no longer regresses that set |

When an effect looks real but small and does not resolve, raise `-n`, or
narrow the measurement to the input set where the change applies (for
example the heavy input that exercises the changed code). Never keep a change
on a run that was not significant.

## Git

- Work on your own branch (see Setup). **Never push, pull, or fetch.**
- `WIP: <summary>` commit messages, with **no Co-Authored-By or other
  attribution lines** (the user's standing rule for regicide). Stage by
  explicit path (`git add src/foo.rs`), never `git add -A`/`.`: untracked
  files like `visualizer-plans/` must not be committed, and `reports/` is
  ignored anyway.
- Each dropped attempt: commit it, tag it
  (`regicide-speedup-NNN/<slug>`), record the sha in
  `unsuccessful/<slug>.md`, then `git reset --hard HEAD^`. The tag keeps the
  sha reachable so the report's reference does not rot. Check `git status`
  is clean before the reset, so only the attempt is discarded.
- The stash is shared with other worktrees and sessions. Do not use it.
- This skill's instructions to commit **are** the user's explicit request to
  commit for the duration of this work. That overrides the default "never
  commit in regicide" rule only for the `WIP` commits and tags described
  here.

## 6. Finish

`report.md` must end with:

- the base sha and the final sha, plus the `WIP` commits in order with
  one-line results;
- the **cumulative** base-vs-tip result on every set, both metrics, with the
  `-n` used and the host load at the time;
- every attempt in a table (kept and dropped), linking to its file;
- what is still hot and the ideas not yet tried, ranked, for the next
  session;
- anything learned that should go into this skill, also in
  `misc/skill-learnings.md`.

Then tell the user where the report is and summarize the cumulative result.

## Pitfalls

- **Believing a stuck replay is a hang.** One input can take minutes.
  Find out which input is running (census, per-input processes) before
  concluding anything.
- **Summing the corpus.** One input dominates the sum. Report per set.
- **Judging a locality change on instructions.** Instructions retired cannot
  see it. Use wall time.
- **Keeping a change because it "must" be faster.** Only significant results
  count.
- **Speeding up event logging.** The `visualizer` feature is on in `run`,
  off in production. Check that the hot code you are optimizing also runs
  in production.
- **Iteration-order changes** from hash containers. Caught by the gate, but
  costly.
- **Measuring with the census or fuzzer running.** Wall time becomes
  meaningless.
- **Counting files with `ls | wc -l`.** `ls` columnizes into a pipe on this
  host. Use `ls -1` or `find`.

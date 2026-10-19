---
name: optimize-regicide-compile-time
description: >
  Profile and optimize how fast `regicide` runs register allocation (its
  compile time), without changing what it allocates. Use when asked to speed up
  regicide, make register allocation faster, reduce regicide's compile-time
  cost, find what is slow or superlinear in regicide, or recover a regicide
  compile-time regression -- driving the work empirically by replaying
  captured corpora with `examples/run.rs` (`--insts`), the `timing` feature,
  a sampling profiler, and disassembly of the hot functions. Produces a
  series of `WIP` commits, one per kept optimization, and a report directory.
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
  Permission is often **scoped** -- "for this attempt only" -- so re-read
  what was granted before each attempt rather than treating it as a new
  default, and say in the commit message that the change was permitted.
  When it is granted, the gate becomes validity (`run --check`, exit 0 per
  set) **plus** a codegen-quality comparison on estimated cycles; see
  "When output changes are allowed".
- **No new `unsafe`**, unless the user explicitly allows it in this session.
- **Statistically significant.** Every kept change has a significant
  improvement on at least one input set and no significant regression on any.
  "It should be faster" is not evidence. See "Measuring".
- **One optimization per `WIP` commit**, and **failed attempts are also
  committed**, so they have a sha for the report, and then dropped from the
  branch (see "Git").
- **Every `WIP` commit message carries its result**: a body summarizing the
  measured speedup per set, or why it was dropped (see "Git: commit
  messages"). The branch should read as its own short report.
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
mkdir -p $R/{successful,unsuccessful,profiles,misc,bins,bench}
```

Not `sets`: `make_sets.py` creates it and refuses one that already exists.

`reports/` is gitignored (by `~/.gitignore`), so nothing in it is committed.

| Path | Holds |
| --- | --- |
| `report.md` | Status, baseline, table of every attempt, cumulative result. Created first, updated after every step. Template in `references/report-templates.md`. |
| `successful/<slug>.md` | One per kept optimization: commit sha, what and why, measurements, links into `profiles/` and `bench/`. |
| `unsuccessful/<slug>.md` | One per dropped attempt: commit sha (it stays reachable from the tag, see "Git"), what, why it failed, measurements. |
| `profiles/` | Raw profiles (`samply`'s `.json.gz`, or `sample`'s text), the reports made from them, timing logs, disassembly. |
| `misc/` | Environment and host load, the census, counters, screens (`misc/screens.md` plus `screened-<slug>.diff`), tool gotchas, and **suggested additions to this skill** (`misc/skill-learnings.md`). |
| `bins/` | A copy of the `run` binary for each commit measured, named `run-<sha>` (and `run-<sha>-prof` for profiling builds). Comparisons need two binaries side by side. |
| `bench/` | Raw per-sample CSVs from `scripts/compare.py`, so any verdict can be re-checked. |
| `sets/` | The input sets (symlinks) from `scripts/make_sets.py`. |

Put the date and time (`date '+%Y-%m-%d %H:%M'`) at the top of every file you
write, and the commit sha every measurement was taken at.

## 0. Setup

1. Create `$R` and a skeleton `report.md` (status: "setting up").
2. **Check the tools exist** and note what is missing in
   `$R/misc/environment.md`: `which samply samply-text rustfilt;
   cargo +nightly fuzz --version`. Several are absent on this host (see
   `references/known-findings.md`, "Tooling facts"), and the fallbacks are
   in "Which functions" below. Finding out now costs a minute; finding out
   mid-attempt costs the attempt's momentum.
3. **Record the environment** into `$R/misc/environment.md`: `date`,
   `git rev-parse HEAD`, `git status --short`, `rustc -V`, `sysctl -n
   machdep.cpu.brand_string hw.ncpu`, `uptime`, and the top of
   `ps -Ao %cpu,etime,comm -r | head -15`. **Load matters.** This host
   normally runs CrashPlan, Defender, and other agents that use whole cores,
   and other Claude sessions may be fuzzing or benchmarking. Write down what
   was running. Re-check before every benchmark and record it with the result.
4. **Branch.** Work on a fresh branch off the current `HEAD`, e.g.
   `git switch -c compile-speedups-NNN`. Note the base sha in `report.md`.
5. **Baseline tests.** Run the test suite on the untouched tree (see
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

  **In a sampling profile it looks much bigger than 0.3%**, because it
  stores and drops wide structs rather than retiring many instructions.
  On `-006`, `PrimaryMap<EventIndex, Event<u16>>::push_unwrap` was **1.9%
  self time, the third-largest row in the whole profile**, with ~0.6%
  more in `drop_glue` and the `u8` variant, and `remap_block_span_events`
  (1.4% of the tree) is `#[cfg(feature = "visualizer")]` outright. Grep a
  new profile for `viz_enabled|events::Event<|EventIndex|remap_` once,
  note the total in `misc/`, and subtract it when reading any share.
- `std` swaps `hashbrown::HashMap` for `std::collections::HashMap` (both with
  `FxBuildHasher`, and the same SwissTable underneath). Close enough, but do
  not tune hashing details off the back of it.
- `insts-retired` (see below) is counted around `regicide::run` only, so
  deserializing the input is excluded. Process wall time is not.

## 2. Census and input sets

The corpora are wildly uneven, and that drives the whole method. Since the
split-pricing fixes of `compile-speedups-002` through `004`, the heaviest
input of `codegen-analysis-006` costs ~1·10¹⁰ instructions (about a second),
so heavy inputs may now be cheap enough to gate and measure on every attempt;
check `sets/sets.md`. Historically, on `codegen-analysis-002`'s six corpora at
`e53b573`:

- **Most inputs cost 10⁶–10⁹ instructions. A few dozen cost 10¹¹–10¹³.**
  The most expensive, `tinygo-regex-0188` (1.1·10¹³ insts, ~15 minutes) and
  `sqlite3-0226` (5.2·10¹², ~8 minutes), each cost more than everything else
  in their corpus put together. Split-point selection was badly
  superlinear on these; since `1f98a23` and `645db2b` the heaviest input
  takes seconds (see `references/known-findings.md`). Re-run the census
  before assuming the old numbers.
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

If an earlier report has a census of exactly the tree you are starting from,
reuse its TSV for `make_sets.py` instead. Spot-check one heavy input's
`--insts` against it first.

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
inputs, and use `--insts` for the comparisons that decide. `--profile`
repeats the inputs and logs every pass of every repeat, so to average out
noise on one small input, sum over a `--profile` run and divide by the
`profiled N pass(es)` count printed in the totals.

### Which functions: `samply-text`, or `sample`

**Check the tools exist before planning around them**, every session: what
is installed changes. As of **2026-10-13**, `samply` and `samply-text`
**are** present and the preferred recipe below works; `rustfilt` is still
**missing**, so `scripts/disasm.sh` needs the `nm`/`objdump` fallback.
(On 2026-10-09 all three were absent and `cargo fuzz` was missing until the
user installed it mid-session.) A minute of
`which samply samply-text rustfilt; cargo fuzz --version` during setup
saves discovering each one at the moment you need it.

The fallback, for when `samply` is missing again, as it did for a whole
session:

```bash
# /usr/bin/sample is always present on macOS.
($R/bins/run-$sha-prof -q --profile 30 <set> >/dev/null 2>&1 &)
sleep 8
sample $(pgrep -n -f "run-$sha-prof") 16 -f $R/profiles/<name>.sample.txt
```

Read `Sort by top of stack` for flat self time and the `Call graph` above
it for the tree. It shows source lines when the binary has line tables.
Symbols come out mangled (v0), so `grep` for the mangled substring --
`10coalescing8coalesce`, say -- rather than the pretty name. There is no
equivalent of `-c`, so deep recursion is harder to read.

For disassembly without `rustfilt`:

```bash
sym=$(nm $R/bins/run-$sha-prof | grep '<mangled substring>' | head -1 | awk '{print $3}')
objdump -d --disassemble-symbols="$sym" $R/bins/run-$sha-prof
```

When `samply` *is* available, prefer it:

```bash
samply record -s -o $R/profiles/<name>.json.gz -- \
    $R/bins/run-$sha-prof -q --profile 30 <input-or-set>
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
- **`--profile SECONDS`** gets enough samples out of anything. `run` reads
  and decodes every input up front, then allocates all of them in whole
  passes until SECONDS have elapsed, printing only on the first pass. A
  typical input finishes in milliseconds, so without this a single input or
  a small set gives too few samples. 30 seconds is plenty for `typical/` or
  one input. A heavy input needs no `--profile`, because one pass already
  takes seconds to minutes. The flag always finishes the pass it is in, so
  on a set holding a heavy input it overshoots by up to that input's time.
- Always pass `-q`, and leave off `--check` and `--insts`. They act only on
  the first pass, but that pass is still in the profile.
- Decoding the inputs still shows up, under `main` but outside
  `regicide::run`: about 1.5 s for sqlite3's 1736 inputs, so ~5% of a
  30-second profile of a set that size. Read percentages of
  `regicide::run`, not of the whole process.
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

- In `src/lib.rs`, the statics and the dump function need
  `#[allow(missing_docs)]`, or the build fails.
- Call the dump after `out.flush()` at the end of `main` in
  `examples/run.rs`.
- Revert with `git checkout src examples`, and check `git status` is clean.

Count before designing, not after. On `compile-speedups-002`, counters
showed 767M span queries for 181k splits (the O(n^2)), that 95% of priced
halves have at most one bundle in the way (the fast path), and that a
suggested fix's target was 0.1% of the time (so it was not worth doing). On
`compile-speedups-004`, counters ruled out two plausible caches in minutes
(reusing a parent split's rows: 7% of rows qualify; filling rows lazily: 96%
of each row is read), and found the RME fixpoint visiting each block 4.8
times.

Counters chase the cheapest thing to count, so also count the *other*
shortcuts a change would disturb. A reordering that skips 5.7M of one kind
of work can lose more by disabling an existing prune that fired more often.

**Count what the work *achieves*, not how often it runs.** A counter
measures operations; what decides an attempt is cycles, and the two differ
by an order of magnitude between a `memmove` and an interpreted loop.
`compile-speedups-006` lost two screens to this, from opposite directions:
**75% of DME's 1.5M operand visits were "wasted"**, and removing them was
worth **0.1%**, because a visit is two field reads on cached data; and
replacing **16.6M element shifts with ~4M** was a **+2.6% to +14.7%
regression**, because one `memmove` of 57 elements beats 57 individual
swaps. In the same session the counter that *found* a win counted an
outcome instead: RME's `kill` removed **0 facts in 120,197 calls**. Zero.

So prefer "how often does this find anything?" to "how often does this
run?", and when a count of operations does look large, convert it to time
with a probe (below) before building anything.

#### Four counters worth running unprompted

Each of these found a kept win, or killed a whole line of enquiry, and each
is a handful of lines:

1. **Visits per block, for every dataflow fixpoint** -- not just the one a
   previous session fixed. Liveness was at **4.54 visits per block** on an
   input whose switch dispatch has 4,097 successors, re-visiting that one
   block ~16,400 times, years after the same pathology was fixed in RME.
   `-92% insts` on that input (`-005`). Check liveness, RME, and anything
   else with a worklist.

   **Measure it across input sizes, and know what a bug looks like.** By
   `-006` all three fixpoints were correctly ordered, yet visits per block
   still *rose* with input size: 1.01 at the smallest inputs to 2.0-2.7 at
   the largest. **That growth is genuine loop convergence, not a bug.** A
   broken worklist order shows as a flat ~4.8 at *every* size. Check the
   pop order by reading the code too: a backwards analysis wants
   post-order (a max-heap on RPO index), a forwards one RPO.
2. **The log-log slope of `insts` against input bytes, per benchmark
   family**, computed straight from the census TSV after `make_sets.py`.
   Every family came out at **1.5 to 2.2** on `-005`; **1.45 to 3.24,
   pooled 1.72**, on `-006`'s corpora. That one number reframed `-005`:
   the gap to ion is an exponent, not a constant factor, so the search was
   for superlinear structure rather than for hot lines.
3. **The same slope per *pass*, not just per family** (`-006`). Bucket one
   big family's inputs geometrically by size, symlink each bucket into its
   own directory, and run the `timing` feature per bucket; a few minutes
   of work gives every pass its own exponent and its share of the largest
   inputs:

   | pass | slope | share of the largest bucket |
   | --- | ---: | ---: |
   | coalesce | 1.85 | 22.6% |
   | generate moves | 1.79 | 20.5% |
   | region allocate | 1.68 | 33.1% |
   | eliminate redundant moves | 1.66 | 13.1% |
   | live ranges | 1.47 | 10.7% |

   This says *which* pass to attack, and whether the exponent is
   concentrated or spread. On `-006` it was **spread across every pass**,
   which correctly predicted that no single structural fix was available
   and that the session would be won in fractions of a percent.
4. **What fraction of a repeated computation is a re-run of unchanged
   input.** `regs_clobbered_across` was recomputed on every queue push, and
   **99.8% of the spans it walked belonged to re-pushes of bundles whose
   spans had not changed** (an eviction changes neither the bundle's spans
   nor the function's reservations). Caching it was `-8.3%` on the input
   where eviction dominates. Ask it of any function called from a loop that
   re-queues work.

## 4. Choose what to try

Rank candidates by **estimated saving × breadth**. A 30% speedup of a pass
that is 2% of `typical/` is worth less than 5% of a pass that is 40% of it.
Record each candidate, its estimate, and the profile evidence in `report.md`'s
backlog before starting on it.

**Probe before building anything.** A throwaway build, measured once with
`--insts` and reverted, converts a guess into a number in two minutes.
There are two kinds, and they fail in different places, so they are worth
treating as separate tools.

**A ceiling probe deletes the work.** The output is wrong; the number is
what a perfect fix could be worth. On `compile-speedups-005`, replacing the
split-point *search* with "cut at the midpoint, price nothing" showed the
search was **22% of `typical/` and 51% of the heaviest input**. That single
number justified the session's largest attempt and would have killed it
just as cheaply had it come back at 2%.

**A marginal-cost probe does the work twice**, and reads the delta as the
cost of doing it once. The output stays correct, and it needs no reasoning
about what breaks, so it works where deleting the work would crash or
short-circuit the pass. On `compile-speedups-006` it was the better tool
three times out of three: RME's `kill` came out at **+0.51%**, and removing
it later measured **-0.526%**; agreement that close is also a check that
the probe measured what it claimed. The same session used it to *reject* a
target: `resolve`'s per-destination hash lookup was only **+0.14%**, though
the 8% around it had looked promising.

**A marginal-cost probe needs a side-effect-free target.** `-008` tried
to double `IntervalSet::try_union` and `check_disjoint` and got
**crashes, not numbers**: the first consumes its sets and rewrites the
arena, the second writes the `boundaries` scratch its caller then reads.
The technique silently assumes the function's only output is its return
value. Where it is not, use a ceiling probe that deletes the work, or
`#[inline(never)]` plus a profiler. The failure mode is at least loud.

**Divide a probe by its call count before believing it.** A probe says
what the work costs, not what removing the *overhead around* it would
save. `-008` probed the eviction path's conflict walk at **+2.38%**,
specialized it exactly as the same change had won in `try_assign`, and
measured **-0.01%**: that walk runs 239,355 times against
`try_assign`'s 1,069,824, so an identical per-call saving is 4.5x less
in total. Count the calls first. (The first explanation for that null
result -- "eviction is rare but heavy" -- was backwards, and the
counters said so. Count rather than reason.)

**Sanity-check a probe against the structure it claims to bound.** A
ceiling probe whose wrong output changes control flow measures something
else entirely: making `block_call_arg` return the first argument read
**-75.8% on `typical/`**, not because the scan was expensive but because
the bad values made the allocator bail out early. If a probe's number is
implausibly large, it broke something rather than skipped it: re-read
what the wrong value does downstream, or switch to a marginal-cost probe.

**Probe a pass wholesale once, to learn whether it is worth having.**
Disabling coalescing entirely (refuse every merge) made the rest of
compilation **51% to 212% slower**. That reframed the pass: the question
was never "can coalescing be cheaper" but "is it doing enough", and it
killed a whole branch of the session's backlog in one measurement. Worth
doing for any pass over ~15% that exists to make later passes cheaper.

### Borrowing a design from ion or regalloc3

`~/regalloc2/src/ion/` and `~/regalloc3` solve the same problems and are
worth reading when regicide looks structurally slow. But:

**The comparison establishes the cost worth attacking, not the fix.** On
`-005` a reading of ion correctly identified that regicide *searches* for a
split point where ion derives one for free from its interference walk. The
recommendation that followed -- copy ion's conflict-derived cut -- was
**wrong, and measurably so: +216% on `typical/`**. Ion's first conflict is
nearly always in the bundle's first span, so the cut peels one span at a
time; ion's bundles leave circulation fast enough not to care, while
regicide requeues the prefix and keeps splitting.

Worse, the borrowed part turned out to be **inert**. Clamping the conflict
towards the middle fixed the blow-up, and sweeping the clamp showed the
tighter it got the better the result on *both* compile time and codegen
quality -- until at the limit the clamp pinned the cut to the middle and
the conflict contributed nothing at all. What shipped ignores the conflict
entirely.

So: probe the cost, then try the borrowed design as **one candidate among
others**, and **sweep its parameters**. A parameter sweep is what revealed
the borrowed part was doing no work. Reading another implementation tells
you what it does, not what it buys here.

Kinds of optimization, roughly in order of how often they pay off here:

- **Delete work that provably achieves nothing.** The cheapest win there
  is. RME's `State::kill` was a `retain` over every fact, run once per
  definition, that removed **0 facts in 120,197 calls**. The preceding
  `clobber` had already taken the definition's own locations, and by SSA
  nothing else can hold a value that is only now being produced. Replacing
  it with a `debug_assert` was **-0.53% insts and -1.81% wall** on
  `typical/`, output byte-identical, and the fuzzer then checked the
  invariant 593k times.

  **The bar is a proof, not a measurement.** In the same session,
  `sequentialize_batch`'s `dedup_by_key` removed **0 of 9.26M** expanded
  moves over the whole corpus, and was deliberately left alone, because
  two group moves in one batch *can* legitimately expand to the same
  `(src, dst)` pair. The corpora merely never contain that shape. Ask what
  guarantees the zero: an invariant of the IR, or the inputs you happen to
  have.
- **Replace a search with an index when the caller asks per something
  denser than the thing searched.** Two of `-006`'s three wins were this.
  `incoming_edges` ran two binary searches over every edge in the function,
  once per live-in span: **208k calls for 1.35 edges of work each**.
  `edge_position` was a pure function of the edge recomputed **10.7 times
  per edge**. Both are now filled in one pass where the data is already
  being sorted. Look for "a sorted array of per-X records, asked about one
  X at a time from a loop over something denser than X".
- **Better big-O.** Superlinear inputs exist (see "Census and input sets").
  Find the loop nest that grows with function size, with a counter, and
  break it: an index instead of a scan, an interval structure instead of
  repeated range searches, incremental update instead of recomputation.

  But **check the superlinearity is not intrinsic** before attacking it.
  Coalescing is the worst-scaling pass (slope 1.85), and its cost is the
  affinity count, which is `edges x live-in set per edge`, and **95.6% of
  the live-in spans it scans produce an affinity**. There is no waste to
  remove; the input really is that big.
- **Stop searching for something you can derive, or balance.** The most
  expensive kind of work here is a search whose answer barely matters.
  `split_between_spans` priced every admissible cut against every candidate
  register -- **22% of `typical/` and 51% of the heaviest input** -- and
  cutting at the middle instead was **-22.6%** *and* slightly better
  codegen. Before optimizing a search, ask whether its result is worth what
  it costs, and probe the ceiling with a throwaway wrong-but-fast version.
- **Fixpoint visit order.** Count analysis visits against reachable blocks
  for **every** dataflow fixpoint, not just the one a previous session
  fixed. A LIFO worklist on a forward analysis made RME visit each block 4.8
  times (15 on one heavy input); visiting in reverse post-order cut the pass
  by 79% and `typical/` by 17.5%. **Liveness had the same bug two sessions
  later**: 4.54 visits per block on a CFG whose switch dispatch has 4,097
  successors, fixed with a post-order heap for **-92% on that input**.
  Identical output either way, since a monotone fixpoint does not depend on
  visit order. Backward analyses want post-order, forward ones RPO.
- **One pass per (collection, query set), not one query per element.** When
  a caller asks a sorted structure about many keys that ascend, the general
  "search per key" shape is `O(keys x log n)` where one merge is
  `O(keys + entries touched)`. This is ion's design (`try_to_allocate_bundle_to_reg`
  carries a comment stating exactly that trade), and the single biggest
  constant-factor family here: the split row fill went from 156 binary
  searches over a ~4,300-entry map to one search plus a sweep (**-2.6%
  typical, -5.2% on the heaviest input**). Note the shape has to *replace*
  the per-key loop -- adding a cursor to it loses (see "The null test").
- **Prune against the best so far, and generalize a prune that works.**
  When a nested search keeps a running best, pass it down as a floor
  (`compile-speedups-004` attempt 2), and look for monotonicity: a split's
  prefix only grows with the cut, so a candidate whose prefix is infinite,
  or already strictly above the best score, can win no later cut (attempts
  6 and 11, -5.1% and then -7.6% of `typical/`). Once a prune is exact for
  a special case, ask what property it really relies on. Mind strict
  versus non-strict at tie boundaries.
- **Remember where the last candidate was blocked.** Loops over candidate
  registers are usually ruled out by the same busy span for neighbor after
  neighbor (87% of failed assignment tries). Checking that span first is
  exact and cheap (attempts 8 and 9, -1.3% of `typical/` each). Keep the
  span itself, not its index into an iterator.
- **Read the shared containers, not just the passes.** When a flat profile's
  largest self-time rows are container internals -- `push`, `capacity`,
  `grow_one`, `memmove`, `drop_glue` -- the fix is in `entity/`, not in the
  caller the row sits under. `compile-speedups-007`'s largest win by far was
  one line there: `SecondaryMap::index_mut` materialized the defaults between
  its length and the key with a `while ... push` loop, re-checking the
  capacity per element; one `Vec::resize` was **-8.7% of `typical/` and -28%
  on the heaviest input**. Six sessions had walked past it because the
  profile names `push_mut<Option<LiveSpan<u32>>>` and `capacity`, never a
  pass. These containers serve every pass, so a line there outweighs any
  single pass.
  `-008` went one level further down and found the session's largest win
  there. **Read what the entity *types* cost, not just the containers**:
  `run_dispatch` tried `u8`, then `u16`, then `u32`, on the assumption
  that a narrower entity means a smaller working set. It does not.
  **`LivePoint<u16>` is the same four bytes as `LivePoint<u32>`**,
  because `LivePoint` packs into `EntityRepr::Wide` and `Wide` maxes out
  at `u32`; `UseData` and `LiveBundleData` barely shrink either. The
  `u16` tier paid for fallible `with_repr32` conversions at 165 call
  sites and got nothing back. Dropping it was **-5.42%**, and dropping
  `u8` as well a further **-1.55%**.

  **One `#[cfg(test)]` test printing `size_of` for every `(type, repr)`
  pair answered in a single compile** what six sessions of profiling had
  not, because the cost shows up as `try_from` (2.5% self) and
  `from_bits` (1.9%) -- rows with no pass name on them. Print them all
  at once; do not binary-search sizes one compile at a time.

  **A tiered "try narrow, fall back" scheme also hides its cost in the
  retries.** Counters put **17-20% of `u8` attempts** at
  `EntityReprTooSmall` *after doing real work* -- **1.9-2.7% of all
  allocation time** that neither the profile nor the timing log shows as
  waste, because an abandoned attempt looks exactly like ordinary
  allocation. Any "optimistic attempt, fall back on failure" structure
  needs a counter on **wall time spent in abandoned runs**, not just a
  count of failures. Note also that the up-front feasibility test
  predicted the wrong thing: it bounds values, insts and registers,
  while what overflows is a span, use or bundle *derived during*
  allocation.
- **Don't recompute.** Does a later pass rebuild something an earlier pass
  already had (liveness, RPO, block-to-region maps, use lists)? Could it be
  kept in the `Context` and reused?
- **Computed per X, but all its inputs are per Y.** Look for a computation
  the code does once per fine-grained thing whose arguments are all
  properties of some coarser thing. `order_non_preferred_candidates` ran a
  counting sort over a register class **per bundle**, but the sort key is a
  function of **the region's** clobber and preference sets alone; caching it
  per (class, region state) hit **97.4%** and was -0.89% of `typical/`. This
  is the general form of `-006`'s `incoming_edges` and `edge_position` wins.
- **Fast path for the common case.** Measure the distribution. If most calls
  see one element, one region, or no conflicts, handle that inline and leave
  the general case to a cold path (`#[cold]`, `#[inline(never)]`).
- **Data structures.** Replace a `BTreeMap` with a sorted `Vec` and binary
  search when it is built once and read many times, or a hash map with an
  entity-indexed `SecondaryMap` when keys are dense, or a `Vec<Vec<_>>` with
  one flat vector plus offsets. Grep the hot passes for `BTreeMap` and
  `BTreeSet` early: on `compile-speedups-004` this was the biggest
  constant-factor win twice (per-unit assignment maps, -12% of `typical/`;
  liveness's value sets with whole-set unions done as one linear merge, -9%
  and -27% on a heavy input). A sorted `Vec` keeps the iteration order, so
  output cannot change.
- **Sort keys.** A `sort_unstable_by_key` whose key closure reads through an
  entity map chases memory on every comparison; packing the key into a
  `u128` beside the entity (with the entity index last, so the order is
  total) is a small, safe win. When the key is already stored inline in the
  sorted elements, packing loses.
- **Layout and size.** Shrink hot types: bit-pack flags, use narrower indices
  (the `EntityRepr` machinery exists for this), use `Option<NonZero…>`, and
  reorder fields. Check sizes with a temporary
  `const _: () = assert!(size_of::<T>() == N);`.

  **Probe the width before shrinking it, and rank the candidates by what the
  probe says.** Add *dead* padding of the size you hope to remove and measure
  the delta; that is what a byte of this map is worth. On
  `compile-speedups-007`, +128 B of padding on `LiveSpanData` cost **+1.36%
  of `typical/`** while +192 B on `LiveBundleData` cost **+0.13%** -- a 10:1
  ratio, found in four minutes, and the *larger* struct was the worse
  candidate. The payoff scales with the map's entry **count** and with how
  much of each entry the hot passes stride over without reading, not with the
  struct's size.

  **`RegSet` is 64 bytes on every machine** (`FixedEntitySet<Reg,
  words_for(Reg::MAX)>` with `Reg::MAX = 512`, against the 128 registers the
  corpora's machines actually define), so grep hot structs for it first.
  Moving `LiveSpanData`'s two `RegSet` hint fields into a side arena -- ~6%
  of spans are ever hinted -- took it from **144 bytes to 16** and was
  **-2.91% wall on `typical/`, -16.12% on heavy/00**, against only -0.60%
  insts.
  **A padding probe prices growth, not a split.** It ranks maps well --
  `-008` found `LiveSpanData` worth **35x per byte** what
  `LiveBundleData` is (+24 B costs +0.22% insts and **+5.79% wall on
  heavy/00**; +192 B of `LiveBundleData` costs +0.05%). It does **not**
  say what moving a field out would buy, because a split adds an
  indirection the padding never had. `-008` tried three and all lost:
  `LiveBundleData::preference` (192 of 240 B) **+0.64%**,
  `LiveSpanData::hints` (4 of 24 B, **0.1% of the map's reads**)
  **+0.39%**, and `LiveSpanData::uses` abandoned (below). The second
  should have worked by every heuristic. It did not, because 24 B to
  20 B crosses no boundary once alignment is counted, where `-007`'s
  span hints went **144 B to 16 B**.
- **Split or group by access pattern.** Which fields of a `PrimaryMap<K, V>`
  are read together in the hot loop? Keep those together in `V` and move
  the cold ones into a `SecondaryMap<K, V2>`. Fields always read together
  belong in one `SecondaryMap<K, (A, B)>`, not two maps.

  Before splitting, check three things `-008` learned the hard way:
  **(a)** the remainder must cross a useful size boundary, not just
  shrink; **(b)** count the *reads*, not the bytes -- a field read six
  times per entry is the wrong thing to put behind a pointer
  (`LiveBundleData::preference` is read 277,084 times against 47,856
  writes); **(c)** check nothing **reorders the map in place**.
  `live_ranges::construct` sorts each block's spans with
  `sort_unstable_by_key` over `self.spans.as_mut_slice()`, which would
  silently desynchronise any `SecondaryMap<LiveSpan, _>` -- the data
  moves and the keys do not. That is what blocked moving
  `LiveSpanData::uses` (8 of 24 bytes, 9.6% of reads) out, and it is
  the one place where the per-byte payoff is highest.
- **Allocation churn.** Reuse buffers kept in the `Context` (it is reset
  between functions, not rebuilt, so cleared vectors keep their capacity),
  avoid `collect()` into a temporary that is immediately iterated, and use
  `SmallVec`-style inline storage only if a dependency is acceptable (ask
  first).
- **Codegen-level.** Remove bounds checks via iterator restructuring, add
  `#[inline]` on cross-module tiny functions, and hoist invariant loads.

Ideas that have **lost** on this data, so think twice before retrying:
galloping or "search near the last hit" instead of binary search (three
times: units of a few hundred entries cost ~8 binary-search steps, and
threading a cursor through the existing per-span call chain costs more than
it saves -- but see the null test under "Screening", which showed the
cursor itself was a win buried under its scaffolding, and led to the bulk
fill that replaced the loop outright); pricing the expensive half of a
split first; walking every per-unit vector to keep its capacity across
resets; a maintained side index over the unit maps (five variants, all
regressions, because the per-insert write costs more than the searches
saved);
an occupancy bitmap in front of a short search (twice now: `-005`'s over
live points at +6.3%, `-006`'s over RME's fact list at +1.9%, where the
null test showed the *branch*, not the maintenance, was the cost);
packing a sort key that is already stored inline in the sorted elements
(twice: `-004`'s `resolve` keys at +0.4%, `-006`'s `dests` at +0.24%);
and skipping a sort when the data is already sorted, where the lists are
short (twice, both flat).

`-008` closed four more, each with measurements rather than a guess, so
**do not re-attempt these without new evidence**: memoizing
`reuse_aware_constraint` (a dense flat-array memo is **+0.30%**, a
`HashMap` one +6.4%, because the repeated calls are the *cheap* ones);
moving a cold field out of `LiveBundleData` or `LiveSpanData` into a
`SecondaryMap` (three tries, +0.64% / +0.39% / blocked); making
`resolve`'s `dests` sort cheaper (four tries -- stable merge +0.33%,
index sort +2.12%, per-value runs +0.81%, no dense key to bucket on --
before the sort was deleted outright); and `SecondaryMap::grow_to`,
where 82% of growths add one element but reserve-ahead is **+1.00%**
and pre-sizing is noise, because the cost is writing 8.6M defaults.

See `references/known-findings.md`.

**Two of those are now three-time losers, and both have the same shape:**
paying a per-element maintenance or staging cost to avoid a search over a
few dozen cached entries. Such a search is ~8 well-predicted steps on data
already in L1. Before retrying anything in that family, use a
marginal-cost probe to show the search is actually expensive.

**A linear fast path in front of a search is now a four-time loser**, and
it is worth stating as a rule rather than a list: *chasing a `next` or
cursor chain is a dependent load per step, where a binary search or treap
descent is predictable, and the steps such a fast path saves are the short
searches that were already cheap.* `compile-speedups-007` found the fourth
instance already in the tree: `last_ending_by` walked up to four `next`
links before descending, averaged **2.03 steps, and still fell through to
the descent 24.2% of the time**, paying for both. Cutting the walk to a
single step was -0.22% of `typical/` and -0.47% on heavy/00.

**The family is now eight losses, and the rule that survives all of
them is sharper than the list.** `-008` added three: an "is there any
`Reuse` at all?" test before `is_reuse_target`'s scan (**flat**),
settling the same per instruction and passing it down (**flat**), and
an `is_empty()` test before `overlapping_reservations`' search
(**+0.31%**) even though **44.7% of unit visits find that map empty**.

*A pre-test pays only when the work it skips is long **and** the test
is cheaper than the work's own early exit.* Rust's slice searches
already exit immediately on an empty slice -- `partition_point` on
nothing is a length load and a return -- so there is nothing left to
skip, and the test only adds an unpredictable branch. In the first two
cases the pre-test **was the same scan** the function would do anyway.

What *does* work on such a function is making each visit cheaper rather
than skipping visits: `-008` took **-1.49%** from `reuse_aware_constraint`
by comparing packed operand bits instead of decoding an
`OperandConstraint` (which built a `RegClass` per operand through a
checked entity conversion).

**Sweep such a bound rather than tuning it.** Sweeping that one over
0,1,2,3,4,6,8,12,16 put 0 and 1 within 0.00% of each other and was
monotone against the rest -- the shipped value of 4 was not merely
suboptimal, it was well past the knee, which one or two spot measurements
around it would not have shown.

**But a sweep ranks only what it measures.** That one measured instructions
retired, and the bound also sets how much *fuel* a check spends:
`last_ending_by` is charged per node visited, so a descent costs
`O(log n)` burns per boundary where a `next` step costs one. Going to 0
rather than 1 was free on insts and made a finely interleaved refusal cost
**~8x more fuel**, which at `RegionFuel::FLOOR` decides whether a merge
happens at all -- a lost merge is a register-register move, in a region
under enough pressure to have spent its budget. Review 003 caught it after
the fact. **When a constant also bounds a budget that decides output, the
sweep's winner is a candidate, not an answer: measure the budget too, and
pin the headroom with a test** (`a_modest_interleaving_still_merges_at_the_floor`).
"Allocation output is byte-identical on the corpus" does not show headroom
is unchanged; it shows no current input reaches the limit.

**A large "falls back to the slow path" share can be the opposite of
opportunity.** `-005`'s bulk row fill covered 38% of rows and bailed out on
the other 62%, which looked like the obvious next win. Extending it lost
3-6%: the per-span path **stops at the first reserved span**, so it was
already cheap on exactly those rows, and a sweep has no such exit. The rows
falling back were the ones never paying full price. Measure what the
fallback *costs on those cases* before chasing its share.

**Count the slow path by the *shape* your special case would catch, not
by how many take it.** `-006` found 59% of `IntervalSet::check_disjoint`
calls falling past its two end-to-end tests into the interleaving walk,
which a marginal-cost probe valued at **1.7% of `typical/`**, the
largest single target of that session. A fast path for the singleton case
bought only -0.07%, because splitting those walks by argument shape showed
**62% are genuine multi-interval merges** and the singleton walks (the
only ones the fast path touched) terminate in one or two steps anyway. One
extra counter, taken before implementing, would have said so.

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
3. **Screen it** (about a minute): build, and run `--insts` once over
   `typical/` and the heavy inputs you bench, against the previous kept
   binary. An idea that is flat or worse here is not worth an attempt:
   revert it, and record it with its diff in `misc/` (see "Screening").
4. **Correctness gate.** See "Testing" and "Correctness gate" below. A
   failure here ends the attempt: it is unsuccessful, whatever its speed.
5. **Commit** as `WIP: <one line on what it does>` (see "Git").
6. **Build both binaries and copy them into `bins/`** (see "Build").
7. **Measure** against the previous kept commit (see "Measuring").
8. **Decide** using the rule below, then **amend the commit message** with
   the result (see "Git: commit messages"). The binaries in `bins/` are
   named by the pre-amend short sha; note the new sha beside the old one in
   the write-up, and copy the binaries under the new name too.
   - **Kept**: write `successful/<slug>.md` and update `report.md`. The next
     attempt's baseline is this commit.
   - **Dropped**: write `unsuccessful/<slug>.md` with the sha, tag it so it
     stays reachable (`git tag regicide-speedup-NNN/<slug> HEAD`), then
     `git reset --hard HEAD^`. Update `report.md`.
9. Re-profile when the profile has plausibly changed, for example after a
   kept win of a few percent or more. The next hot spot is often not the
   one you expected.

Every few kept commits, and always at the end, also measure **the original
base against the current tip** on every set. This gives the cumulative
number, and catches individually-insignificant regressions that add up. It
also confirms small wins: on `compile-speedups-004`, four attempts of
0.35-1.3% each never resolved on wall time alone, but their cumulative
(n=30) resolved at -6.7% wall on `typical/`.

### Screening

When the user caps the number of attempts, a screen costs no attempt, so
use it freely: `compile-speedups-004` rejected seven ideas this way and
`-005` ten, several of them large regressions (+6.3%, +5.0%, +29%). One
`--insts` sample per build is noisy at the ±0.2% level on heavy inputs, so
a screen of a few tenths of a percent decides nothing; only commit those if
the idea is cheap. Record every screen (idea, deltas per set, diff path) in
`misc/screens.md`, and save the diff with `git diff > $R/misc/screened-<slug>.diff`
before reverting.

**Screen on the whole `typical/` set, not a sample.** A sample of every
40th input (825 of 13,922) disagreed with the full set repeatedly on
`-005`, and in both directions: one idea looked like a win on the sample
and a loss on the set, another -2.07% on the sample and -2.67% on the set.
A full `--insts` pass costs ~20 s. The per-family sets in `misc/` are for
diagnosis, not for verdicts.

**A failed screen is evidence, not just a rejection.** Two of `-005`'s kept
attempts came out of what a failed screen taught, so write down *why* it
failed, not only that it did.

#### The null test

When a change regresses, **disable its new logic but keep its code shape**,
and measure again. The difference separates "the idea is wrong" from "the
scaffolding costs more than the idea saves".

On `-005` a cursor threaded through the interference query regressed 1-5%.
Raising its threshold so the cursor **never fired** still cost +0.55% to
+0.92% -- so the whole regression was the extra parameter, the
`mem::take`/put-back, and the second routine competing for inlining, and
the cursor itself was worth about -3.1% underneath it. That reading is what
led to the attempt that *did* work: replace the per-span call loop entirely
rather than speed up its iterations. Without the null test the obvious
conclusion -- "cursors lose here", which two earlier sessions had already
recorded -- would have been wrong for the third time.

**When the null test says the scaffolding is cheap, ask whether the cost is
in the new algorithm or in the branch that selects it.** On
`compile-speedups-006` it answered both ways within an hour:

- Merging a bundle's span run into a unit regressed +2.6% to +14.7%, and
  the null test cost only **+0.15%**: the algorithm itself was wrong here
  (one `memmove` beats 57 swaps).
- An occupancy bitmap for RME's `clobber` regressed +1.9%, and keeping all
  its maintenance but never letting the fast path fire cost **+0.33%**,
  so the *fast path itself* cost the remaining ~1.5%. It put a 27/73
  data-dependent branch in front of a `partition_point` over 13.5 cached
  entries.

That second shape is worth naming: **a fast path needs the work it skips to
be long, not merely often skippable.** Replacing a short, well-predicted
search with an unpredictable branch loses even when the branch "saves" the
search three times in four. (Note the exception in the same measurement:
on `hashset`, where the fact lists are far longer, the identical change was
**-0.6%**.)

### Overlapping work

Fuzzing (700 s) is the critical path of an attempt. Implementing, counting
and screening the next idea while the previous one fuzzes keeps things
moving, with two rules:

- **Never edit `src/` while `cargo fuzz` is still compiling.** On
  `compile-speedups-004` a fuzz build picked up a deliberately broken
  mutation check of the *next* idea from the working tree and reported a
  crash that did not exist in the commit. **`-007` hit it again** -- a
  screen written into `src/interval_sets.rs` produced a
  `refused as overlapping, but the sets are disjoint` panic at 1,024
  execs that did not reproduce at the commit, nor with the finished
  screen applied, and a clean re-run then did 424k runs green.

  The window is the whole build, which is ~2 minutes, while `INITED` can
  be ten minutes later on this corpus -- so "wait for `INITED`" is a long
  wait and easy to talk yourself out of. **The reliable discipline is to
  not touch `src/` at all until the fuzz run has printed `Done`**, and to
  do the next idea's reading, counting and design in that window instead.
  Treat any fuzz crash as suspect until it reproduces on a clean tree at
  the commit under test.
- **Do not run the wall-time measurement while anything else runs.** The
  previous attempt's measurement waits for its fuzz to finish; then the
  next attempt's gate and fuzz start after the measurement.

Binaries are copied per commit, so a measurement never depends on what is
in the working tree.

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
At `7e8f866` it is 428 + 8; `compile-speedups-005` left it at 430 + 8.

**`cargo test --all-features --no-run` is the cheap version of that check**
(a few seconds, no test execution). Run it immediately after any change to
a function's signature. Adding one out-parameter to `try_assign_to_reg` on
`-005` left `cargo build` green and broke eight `#[cfg(test)]` call sites.

**When a test fails, re-run on a known-clean tree before explaining it.**
`-005` made this mistake in both directions on the same day: once blaming a
race for six genuine failures (a real aliasing bug), and once nearly
accepting eight failures that really were a race with a mutation check in
the tree. A failure list spanning unrelated modules is **not** evidence of
a race -- it is what a broken invariant deep in the allocator looks like.
Restore the tree, confirm the release binary matches the one you screened
(`cmp`), and only then form a theory.

If the change touches anything the fuzzer exercises (most of the allocator),
also run the `allocate` fuzz target. The user's notes require `-s none`,
libFuzzer flags after `--`, and enough `-max_total_time` to get past corpus
loading (roughly 410 s). Run it in the background while you measure:

```bash
cargo +nightly fuzz run -s none allocate -- -max_total_time=700 \
    > $R/misc/fuzz-<sha>.log 2>&1; echo "exit=$?"
grep -E 'INITED|DONE|Done [0-9]+ runs|ERROR|panicked' $R/misc/fuzz-<sha>.log
```

Require `INITED` and `Done` before calling it clean. A foreground run of
700 s outlives the Bash tool's 600 s limit, so start it in the background
and wait on `exit=` in its log.

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

When the user has allowed output changes, identity is not the gate. Run
`run --check -q` once per set directory and require exit 0 from each, on top
of the tests and the fuzzer.

**Tests do not prove identity.** A property test compares a new structure
against the old function on generated states, which covers shapes the
kernel never produces and can miss some it does. On `compile-speedups-002`,
a property check first built halves the kernel never creates, and an
earlier one would have missed out-of-order candidate queries. Run the gate
even when the tests are thorough, and mutate the new code once (break one
line, confirm a test fails) to check the test can see it.

Expect the mutation to pass more often than not on a new fast path. On
`compile-speedups-004`, five of fifteen attempts needed a new test or test
case before a deliberate bug failed (an interleaved merge where the existing
test only appended, a run of cuts broken by one whose candidates all fall
below the floor, a span set long enough to be walked from both ends,
`btree.rs` with no tests of its own). Add the test. For a pure refactor
where no reasonable test can see the mutation (an equivalent condition kept
for safety), say so in the write-up: the gate is then the real check, and
the write-up should not claim test coverage.

### Making the mutation check mean something

- **Confirm the edit landed.** A mutation that "passes" may never have been
  applied: on `-005` `cargo fmt` reflowed an expression after the patch was
  written, so its match string no longer existed, and the suite ran against
  unmutated code. It looked like a real coverage gap. `grep` for the
  mutation, or have the patch script assert, before believing a pass.
- **If you cannot make a mutation fail, check the new code runs at all.**
  An `eprintln!` in the new branch, counted over a test run, answers it in a
  minute. On `-005` an eviction shortcut's precondition **never fired once**
  in a 2,000-iteration property run; three added seeds and a hand-written
  unit test all failed to reach it. The tests were not weak -- the generator
  could not reach that state. That is worth knowing before writing a fourth
  test.
- **Prefer a `debug_assert` to a new test case.** Asserting the invariant
  at the point it must hold lets the *existing* generator find the bug,
  because it usually already produces the shapes; it just has no way to
  notice. On `-005` a one-line `debug_assert` that no assignment survived
  outside the units given caught the real bug **and** two bugs in the test
  harness written to catch it. Measure the assert's cost if it is in a hot
  path -- that one was free.

  **For a cache, it is usually not a preference but the only option.**
  `compile-speedups-007` cached a per-region ordering; dropping the
  invalidation test for the one input that can change under it **passed the
  whole suite and left the output byte-identical on 600 `typical/` inputs
  and two heavy ones**, because a counter put that case at **27 of 66,885
  asks (0.04%)**. No corpus of this size will catch that by differing
  output. A `#[cfg(debug_assertions)]` block that recomputes the cached
  value and compares made the same mutation fail *immediately and across
  many unrelated tests*. **Any cache whose staleness window is rarer than
  about 1% should carry one**, and the fuzz target builds with debug
  assertions, so it then gets checked hundreds of thousands of times.
- **A mutation that produces identical output may be correct.** Bucketing a
  sort on `key >> 97` instead of `>> 96` merges two values per bucket and
  changes nothing, because each bucket is still sorted within itself.
  Record it as a mutation that *should* pass rather than as a gap.
- **But identical output is never proof that an invariant holds.** It says
  the corpus did not notice. `-007`'s one failed attempt guarded an
  all-operands scan with `kind() == DefUse::Def`, screened at **-0.92% of
  `typical/`** with **byte-identical output on 600 inputs** -- and the
  guard was logically inverted: `validation.rs`'s `InvalidReuse` rules
  require a `Reuse`'s target to be an early *use*. The speedup was the
  guard skipping work it should have done. Corrected, it was worth 0.08%.
  **When a change rests on an invariant about the IR, check it against
  `validation.rs`, which states these rules explicitly**, before believing
  a clean gate.

### When output changes are allowed

Identity is not the gate; validity and codegen quality are. Run
`run --check -q` per set and require exit 0 from each. Also compare
**estimated cycles**, which is the metric the user's codegen-quality work
is measured against -- `run -q <set>` prints it in the totals. A
compile-time win that costs cycles is a trade the user has to approve; one
that improves them is not a trade at all.

`compare.py` prints `ALLOCATION COUNTS DIFFER` instead of its usual
agreeing line, so any loop waiting on the agreeing phrase will hang. Also
re-check which tests assert that a *case is still reachable*: on `-005` one
variant of an output-changing attempt silently stopped producing the
allocation shape that reaches a guard in `hoist_demanded_moves`, leaving it
untested across the whole corpus. The test failure was evidence about the
change, not a stale test, and it discriminated between two variants that
looked identical on every aggregate number.

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

**A wall delta several times the insts delta is the signature of a locality
change, not an error.** `-007`'s span-shrinking attempt measured -0.60%
insts and **-2.91% wall on `typical/`, -16.12% on heavy/00**: the same
instructions retiring against a working set that now fits. So do not skip
the wall run because the insts figure looks too small to bother with -- on
a layout change that figure is the one carrying no information.

```bash
python3 $S/compare.py -n 20 --csv $R/bench/<slug>-typical.csv \
    $R/bins/run-<base> $R/bins/run-<cand> $R/sets/typical \
    | tee $R/bench/<slug>-typical.txt
python3 $S/compare.py -n 10 --csv $R/bench/<slug>-heavyNN.csv \
    $R/bins/run-<base> $R/bins/run-<cand> $R/sets/heavy/NN-* \
    | tee $R/bench/<slug>-heavyNN.txt
```

`compare.py` prints a `round N/M done` line per round; add
`| grep -v '^round'` before `tee` to keep the saved result readable.

**Use `-n 5` or more.** With 3 samples per build, Mann-Whitney's p can never
go below 0.081, even when every candidate sample beats every baseline
sample, so `-n 3` can never come out significant. `-n 6` reaches p=0.0051.

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
  and the memory bus. Run the correctness gate during `insts`-only
  screening if you must, but **not** during the wall-time run that decides.
- Other sessions can push the load from ~8 to ~90 in minutes. At load
  56-87, `typical/` wall CV reached 72-92%, and wall could not resolve
  effects under ~10%, though insts still resolved 3%. Record `uptime` with
  every result.
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

### Layout noise on a single heavy input

**Before dropping a change that regresses one heavy input by under about
half a percent, run the null test.** `-008` nearly lost a good change
this way. Attempt 8 measured a significant **+0.34% on heavy/01**, which
the table above says to drop. But the pass it touched is **3.1% of that
input**, so +0.34% of the whole would need that pass to be 11% slower --
and the `timing` log showed it *flat*, while **region allocate**, a pass
the change does not touch, moved by ~5 ms.

The null test settled it: the same code shape with the optimization
disabled, computing exactly what the baseline computed, measured
**-0.385%, +0.398%, +0.180%** on the three heavy inputs. **A change that
computes the same thing moved them by +/-0.4% through layout alone.**

`--insts` has ~0.02% CV on a single heavy input, so `compare.py` reports
a 0.2-0.4% layout shift as "SIGNIFICANT (SLOWER)" at p=0.0002. It is
statistically significant and causally meaningless. On `typical/` this
does not arise, because 13,925 inputs average the layout lottery out; on
*one* input there is nothing to average.

So, for a sub-0.5% regression on a single heavy set:

1. Check the `timing` log. If the regressing input barely runs the pass
   you changed, suspect layout immediately.
2. Run the null test. If it reproduces the regression, the measurement
   is telling you nothing about your change.
3. `#[inline(never)]` and moving the branch elsewhere do **not** help --
   `-008` tried both; the sensitivity is inherent.

This also means a sub-0.1% figure on one heavy input is **below the
noise floor** and should not be reported as an effect in either
direction.

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

### Commit messages

The subject says what the change does; the body says what it bought. Write
the body once the verdict is in, by amending the attempt's commit
(`git commit --amend -F <file>`, since the attempt is always `HEAD` at that
point), before tagging or moving on. Keep it short: a sentence or two on
the idea, then one line per set, then the verdict. Wrap at 72 columns, no
attribution lines.

```
WIP: Skip split candidates whose prefix already costs more than the best

A split's prefix only grows with the cut, so a candidate whose prefix
already exceeds the best score's interference can win no later cut.
Skips 18.6M of 28.6M prefix pricings on typical.

Measured against previous commit (ff9269d), n=20, 99% CI:
* typical:  insts -7.60%, wall -5.11%
* heavy/00: insts -10.30%, wall -6.76%
* heavy/01: insts -10.52%, wall -6.48%
```

- Give each set's insts and wall deltas from `compare.py`. Write `(not
  significant)` for any that is not significant, never a bare number that could
  be mistaken for a result.
- Name the baseline commit by its sha.
- For a dropped attempt, say so in the body's last line and why
  ("Dropped: no measured effect on any set"), so the tagged commit explains
  itself.
- If the user rewrites the branch between sessions, keep the bodies; they
  are how the next session knows what each commit is worth.

## 6. Finish

`report.md` must end with:

- the base sha and the final sha, plus the `WIP` commits in order with
  one-line results (the commit bodies hold the full per-set numbers);
- the **cumulative** base-vs-tip result on every set, both metrics, with the
  `-n` used and the host load at the time;
- every attempt in a table (kept and dropped), linking to its file;
- **every screen in a table too**, with its deltas and why it failed, and
  **every probe** with what it bounds. On a flat profile these outnumber
  the attempts several to one and are most of what the next session can
  use: `-006` kept 3 and screened 10.
- what is still hot and the ideas not yet tried, ranked, for the next
  session, **with a measured ceiling wherever a probe gave one**;
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
- **Implicit call-order contracts.** A cache filled "when the caller asks
  about candidate N for the first time, which is right after N-1" breaks,
  in release with an out-of-bounds panic, as soon as a later optimization
  skips a candidate. Index caches by key, and fill on first use in any
  order.
- **Inlining a one-time fill into a hot function.** It cost +1.4% insts on
  `typical/`. Split it out as `#[cold] #[inline(never)]` and keep the hit
  path `#[inline]`.
- **The branch moving under you.** The user may rebase or reword your
  commits between turns (the WIP prefix gets dropped, shas change). Before
  building on it, check `git log`, and compare patches by content
  (`git show <old> --format=` vs `<new>`) rather than trusting shas in the
  report.
- **A cheaper-looking variant can cost more.** Recomputing a bound as
  `best.max(floor)` every iteration pruned more work than a running bound
  updated on improvement, but retired 3.8% *more* instructions. Screen
  variants on instructions, not on counts of skipped work.
- **Scripted edits that half-apply.** A Python edit that asserts on a
  pattern stops after its first replacement; re-running it on the
  already-edited file fails the assert and leaves the build broken, and a
  screen that follows then measures a stale binary. Check that the build
  printed `Finished` before trusting a screen, and reset the file before
  retrying an edit.
- **A fuzz crash from a dirty tree.** See "Overlapping work".
- **Inserting an item above an existing one steals its attributes.** A new
  function or test written directly after an existing item's doc comment
  takes that doc -- and any `#[cfg(...)]` with it -- because Rust attaches
  outer attributes to the *next* item. A review of `compile-speedups-005`
  found this three times in eight commits, once silently un-gating a test
  that cannot compile without the `visualizer` feature. **Nothing catches
  the `cfg` half**: `cargo doc --all-features` sees the orphaned doc, and
  the dev-dependency feature unification hides the `cfg` from every CI row
  that builds tests. It is a hazard of patching files by string insertion.
  After inserting an item, read what sits immediately above the insertion
  point and confirm the item *below* still owns its docs and attributes.
- **`pgrep -f <pattern>` matches your own waiting loop.** `until ! pgrep -f
  'check_identical.sh'; do sleep 10; done` never exits, because the loop's
  own command line contains that string. This looked twice like a gate
  running long after it had finished. Wait on the log's contents instead:
  `until [ "$(grep -c 'identical\|DIFFERENT' $R/misc/ident-a2.log)" -ge 4 ]`.
- **Waiting on a phrase only one code path prints.** `compare.py` ends with
  `allocation counts identical: ...` when the builds agree and
  `ALLOCATION COUNTS DIFFER ...` when they do not. A monitor watching for
  the first sat through a full 30-minute timeout on a run that had finished
  25 minutes earlier. Match something both paths print (`=>`, or `COUNTS`),
  or wait for the process to exit.
- **A sample of `typical/` is not `typical/`.** See "Screening"; they
  disagreed in both directions on `-005`.
- **Reading a count of operations as a count of time.** The two differ by
  an order of magnitude between a `memmove` and an interpreted loop. See
  "How often: counters"; it cost `-006` two screens.
- **A ceiling probe whose wrong output changes control flow.** It then
  measures the allocator taking a shortcut, not the work you skipped.
  `-006` saw -75.8% from a probe that was really making the allocator bail
  out early. Sanity-check the number against the structure it claims to
  bound, and prefer a marginal-cost probe when deleting the work would
  break an invariant.
- **Interleaved stdout and stderr when dumping counters.** `run` writes
  results through a `BufWriter` on stdout while counters go to stderr, so
  `run ... 2>&1 | grep CTR` splices the two mid-line and mangles both.
  Redirect separately: `run -q <set> >/dev/null 2>/tmp/ctr.txt`.
- **Leaving a fuzz worker running into a measurement.** `cargo fuzz`'s
  child survives the parent's exit and sits at 100% of a core. Check
  `ps`/`uptime` and `pkill -f 'release/allocate'` before any wall-time
  run; `-006` caught one only because the load average looked wrong, and
  `-007` hit it twice (`pkill -9` is what finally cleared it).
- **A screen is not a verdict about correctness.** It only says the
  candidate is faster, and the fastest way to be faster is to do less than
  you should. `-007` screened an idea at -0.92% whose guard was logically
  backwards; the gate was clean too, because the corpus never exercises
  the difference. Check the invariant, not just the numbers.
- **A hanging test is a detection, not a timeout.** `-007`'s mutation of
  the treap descent made `unions_match_a_model` loop forever instead of
  failing an assertion. Under plain `cargo test` that just looks stuck.
  Note that **`timeout` is not installed on this host**: to bound a run,
  `cargo test --no-run` and execute the test binary in the background,
  polling its log.
- **An empty heredoc body truncates the file.**
  `cat >> report.md <<'EOF'` followed immediately by `EOF` writes
  nothing and leaves the file **empty**. `-008` lost `report.md` that
  way mid-session and rebuilt it from the per-attempt files, which were
  intact. Append with a non-empty body, or edit with Python.
- **A test that hangs forever rather than failing.** Already noted
  below for `timeout`; `-008` adds that a *mutation* can do this too.
- **Re-blessing a fixture can touch more files than the failure named.**
  `-008`'s attempt 16 reordered the visualizer event log; the test
  named one fixture, but `REGICIDE_BLESS_FIXTURE=1` rewrote **six**.
  Check `git status` after blessing, and verify each: comparing the
  JSON as a *multiset* of events proved all six were pure reorderings
  with nothing added or removed, which is what made the change safe to
  keep.
- **Parsing `--insts` with a bare `grep`.** `run` prints `insts-retired`
  once per input *and* again under `=== totals`, so a single-input set
  gets double-counted. Use
  `awk '/=== totals/{t=1} t&&/insts-retired/{print $2; exit}'`.

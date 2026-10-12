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

**Check the tools exist before planning around them.** On this host, as of
2026-10-09, `samply`, `samply-text` and `rustfilt` are **not installed**,
which breaks the recipe below and `scripts/disasm.sh` with it. `cargo fuzz`
was missing too until the user installed it mid-session. A minute of
`which samply samply-text rustfilt; cargo fuzz --version` during setup saves
discovering each one at the moment you need it.

The fallback, which carried a whole session:

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

#### Three counters worth running unprompted

Each of these found a kept win on `compile-speedups-005`, and each is a
handful of lines:

1. **Visits per block, for every dataflow fixpoint** -- not just the one a
   previous session fixed. Liveness was at **4.54 visits per block** on an
   input whose switch dispatch has 4,097 successors, re-visiting that one
   block ~16,400 times, years after the same pathology was fixed in RME.
   `-92% insts` on that input. Check liveness, RME, and anything else with
   a worklist.
2. **The log-log slope of `insts` against input bytes, per benchmark
   family**, computed straight from the census TSV after `make_sets.py`.
   Every family came out at **1.5 to 2.2**. That one number reframed the
   session: the gap to ion is an exponent, not a constant factor, so the
   search was for superlinear structure rather than for hot lines.
3. **What fraction of a repeated computation is a re-run of unchanged
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

**Probe the ceiling before building anything.** A deliberately-wrong fast
version, run once and thrown away, tells you what the real fix could be
worth. On `compile-speedups-005`, replacing the split-point *search* with
"cut at the midpoint, price nothing" -- wrong output, reverted immediately
-- showed the search was **22% of `typical/` and 51% of the heaviest
input**. That single number justified the session's largest attempt and
would have killed it just as cheaply had it come back at 2%.

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

- **Better big-O.** Superlinear inputs exist (see "Census and input sets").
  Find the loop nest that grows with function size, with a counter, and
  break it: an index instead of a scan, an interval structure instead of
  repeated range searches, incremental update instead of recomputation.
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
- **Don't recompute.** Does a later pass rebuild something an earlier pass
  already had (liveness, RPO, block-to-region maps, use lists)? Could it be
  kept in the `Context` and reused?
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

Ideas that have **lost** on this data, so think twice before retrying:
galloping or "search near the last hit" instead of binary search (three
times: units of a few hundred entries cost ~8 binary-search steps, and
threading a cursor through the existing per-span call chain costs more than
it saves -- but see the null test under "Screening", which showed the
cursor itself was a win buried under its scaffolding, and led to the bulk
fill that replaced the loop outright); pricing the expensive half of a
split first; walking every per-unit vector to keep its capacity across
resets; a maintained side index over the unit maps (five variants, all
regressions -- the per-insert write costs more than the searches saved).
See `references/known-findings.md`.

**A large "falls back to the slow path" share can be the opposite of
opportunity.** `-005`'s bulk row fill covered 38% of rows and bailed out on
the other 62%, which looked like the obvious next win. Extending it lost
3-6%: the per-span path **stops at the first reserved span**, so it was
already cheap on exactly those rows, and a sweep has no such exit. The rows
falling back were the ones never paying full price. Measure what the
fallback *costs on those cases* before chasing its share.

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

### Overlapping work

Fuzzing (700 s) is the critical path of an attempt. Implementing, counting
and screening the next idea while the previous one fuzzes keeps things
moving, with two rules:

- **Never edit `src/` while `cargo fuzz` is still compiling.** Wait until
  its log shows `INITED`. On `compile-speedups-004` a fuzz build picked up a
  deliberately broken mutation check of the *next* idea from the working
  tree and reported a crash that did not exist in the commit. Treat any
  fuzz crash as suspect until it reproduces on a clean tree at the commit
  under test.
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
- **A mutation that produces identical output may be correct.** Bucketing a
  sort on `key >> 97` instead of `>> 96` merges two values per bucket and
  changes nothing, because each bucket is still sorted within itself.
  Record it as a mutation that *should* pass rather than as a gap.

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

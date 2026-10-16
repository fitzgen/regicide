# Known findings

What earlier sessions established about where regicide's compile time goes.
Each item has the date, the sha it was measured at, and its status. Re-verify
anything you are going to build on: regicide changes quickly, and a finding
can be fixed by someone else between sessions. Add to this file (via
`misc/skill-learnings.md`, for the user to fold in) whenever a session
learns something durable.

## The workload is extremely skewed (2026-10-05, `e53b573`; updated 2026-10-06)

Census of the six corpora in `~/regalloc2/reports/codegen-analysis-002/`
(4,120 inputs) with `scripts/census.py`:

Measured: 4,119 of 4,120 inputs. The last, `tinygo-regex-0117`, was still
running after 18 minutes when this was written, so it is heavier than
anything below.

| input | insts | wall (9 jobs in parallel) |
| --- | ---: | ---: |
| `tinygo-regex-0117` | > 1.1·10¹³ | > 18 min (unfinished) |
| `tinygo-regex-0188` | 1.10·10¹³ | 881 s |
| `tinygo-regex-0107` | 5.23·10¹² | 486 s |
| `sqlite3-0226` | 5.17·10¹² | 508 s |
| `tinygo-regex-0252` | 3.67·10¹² | 294 s |
| `tinygo-regex-0047` | 2.35·10¹² | 218 s |
| `tinygo-regex-0103` | 9.07·10¹¹ | 81 s |
| `tinygo-regex-0178` | 7.21·10¹¹ | 70 s |
| `shootout-sieve-0061` (= `switch-0063`) | 5.40·10¹¹ | 44 s |
| `sqlite3-1599`, `sqlite3-1521` | 4.7, 4.2·10¹¹ | 41, 35 s |
| `shootout-switch-0004` | 3.76·10¹¹ | 28 s |

24 inputs took over 10 s. Two thirds are `tinygo-regex`, from a corpus of
310. Good mid-weight benchmark inputs, which resolve in one sample but don't
take all afternoon: `shootout-switch-0004`, `shootout-sieve-0061`,
`tinygo-regex-0103`.

- Most inputs cost 10⁶–10⁹ instructions and allocate in milliseconds.
- **A few dozen inputs cost 10¹¹–10¹³+** and take tens of seconds to over 15
  minutes each, many from files of ~60KB. These are the clearest targets for
  a big-O fix. Size on disk
  predicts little: the 296KB `sqlite3-0780` is not among the worst.
- `shootout-sieve-0061` and `shootout-switch-0063` are byte-identical, and
  `make_sets.py` dedups them.

**Status:** mostly fixed. The superlinearity was in splitting (see the next
two sections). After `1f98a23`, only 25 inputs are still over 10^10 insts,
the heaviest `tinygo-regex-0117` at 4.7e11 (52 s); at `645db2b` it is 5.2e10
(3.8 s). `tinygo-regex-0117` took 1,854 s at `ce351b4`, much more than the
">18 min" above.

## Hot spot on a heavy-ish input: `split_between_spans` (2026-10-05, `e53b573`)

`samply` over 40 replays of `shootout-sieve-0020` (1.2·10⁹ insts each, a
mid-sized input, not even a heavy one):

- 99.5% `run_inner<u16>`, of which **93% is
  `RegionAllocation::split_between_spans`**, and inside it a closure that
  calls `Assignments::interference_weight`.
- ~50% of all samples are self time in
  `BTreeMap::range` → `find_leaf_edges_spanning_range` over
  `BTreeMap<AssignmentKey, Assignment>`, and ~6% more in the same over
  `ReservationEntry` (`overlapping_reservations`).
- In other words, split-point selection asks the per-register assignment
  B-trees "what overlaps this range" once per candidate split point per
  register. That pattern is O(candidates × registers × log n), and each query
  is a cache-unfriendly B-tree descent. Candidates: cache or incrementally
  maintain the interference per candidate, sweep the candidates in order
  with one forward cursor per register instead of a fresh `range()` each
  time, or prune registers early.

Timing log for the same input (fixed formatting): region allocate 89.8 ms,
generate moves 1.3 ms, coalesce 1.2 ms, eliminate redundant moves 0.9 ms,
live ranges 0.8 ms, everything else < 0.35 ms each. **Region allocation is
~95% of this input's time.**

**Status:** fixed (2026-10-06). Two causes, fixed separately:

1. Tie-breaking: earliest-of-equals cuts peeled one span per split, so a
   bundle took O(spans) splits. Fixed by taking the middle of the first run
   of tied cuts (`a183083` between spans, `1f98a23` within spans). Those
   **change output**, and the user allowed it for that session.
2. Each split priced both halves of every cut span by span: n(n-1) B-tree
   queries per candidate per split. Even after (1), `split_between_spans`
   was 71% of `typical/`. Fixed without changing output on
   `compile-speedups-002`; see the next section.

## Split pricing: per-span conflict cache (2026-10-06, `645db2b`)

On branch `compile-speedups-002`, five commits `5e2b0d6`..`645db2b` on top of
`36e91a7`. Allocation output byte-identical. Base `1f98a23` vs the
pre-review tip: `typical/` insts -74.4%, wall -65.3% (17.0 s -> 5.9 s);
`tinygo-regex-0103` -83% wall; `tinygo-regex-0117` 33 s -> 3.8 s.

- **A span's conflicts in a register do not depend on the cut.** So
  `SpanInterference` (`src/region_allocation/assignments.rs`) queries each
  span once per candidate register, appending its conflicts to one flat
  vector in span order. A half is "undivided spans `a..b` plus one divided
  span", so its conflicts are one slice, found through a per-candidate prefix
  array that also counts reserved spans. Only a divided span the cut clipped
  or widened is queried afresh (607k of 65.5M pricings on `typical/`).
- **95% of priced halves have at most one distinct bundle in the way**, often
  repeated over many spans. A `run_starts` array answers "is this slice one
  bundle?" in O(1), skipping the copy, sort and dedup.
- **Spans between a candidate's first and last reserved spans are never
  queried**: every half holding one also holds a reserved span, so it is
  infinite anyway. -22.6% of fill queries on `typical/`.
- **A candidate whose prefix alone already scores below the best is
  skipped** without pricing its suffix (`best_candidate` in `splitting.rs`).
- Bit-identical f32 sums: the summed set and order (sorted by bundle) are
  unchanged. `Iterator::sum` on f32 starts at `-0.0`, so a fast path must
  use `.sum()` too, not a literal `0.0`.
- Keep the fill out of line (`#[cold] #[inline(never)] fill_row`): inlined
  into `weight`, it cost +1.4% insts on `typical/`.

**Where the time goes at `645db2b`** (`typical/`, 2,674 inputs):

| pass (timing log) | ms | share |
| --- | ---: | ---: |
| region allocate | 2829 | 62% |
| eliminate redundant moves | 661 | 14.5% |
| generate moves | 327 | 7.2% |
| coalesce | 216 | 4.7% |
| live ranges | 205 | 4.5% |
| liveness | 131 | 2.9% |

samply, share of the whole process (~83% is `run_dispatch`, ~15.5% is
reading and decoding inputs): `split_between_spans` 26.8% (of which B-tree
fill queries via `push_interfering` 11.6%), `assign_via_eviction` 13.0%,
redundant-move `analyze` 10.5%, `assign_to_non_preferred` 6.5%,
`generate_moves` 4.8%.

**Status:** mostly done by `compile-speedups-003` and `-004` (see the
section at the end). Items 1, 3 and 5 were done in 003; item 4 was tried
in 004 and lost (pricing the suffix first gave up the prefix prune, +5.4%);
item 2 was counted in 004 and only 7% of rows qualify. Original list:

1. `assign_via_eviction`: 8.1M candidate probes making 42M B-tree span
   queries for only 48.5k evictions on `typical/` (counted at `777c130`).
   `sole_conflicting_bundle` already stops at a second bundle, so the cost
   is the queries before that.
2. Fill queries: a bundle split repeatedly re-fills its surviving spans
   each time. When nothing was assigned in between, a half's conflicts are
   a slice of its parent's. Needs an "assignments unchanged" generation
   counter.
3. Redundant move elimination: `clobber` is a `retain` over all facts per
   edit, and `range_of` does two binary searches (its own TODO suggests
   galloping).
4. Price the half more likely to lose first, so the prune in
   `best_candidate` skips more.
5. Crowded halves (two or more distinct bundles) still copy and sort the
   whole slice per cut: O(spans^2 log) for such a bundle. Measured cheap on
   these corpora (3.5% of pricings, ~0.1% of samples), so a left-to-right
   sweep with per-bundle multiplicity counts was not worth it yet.

## Liveness is superlinear on `shootout-switch-0004` (2026-10-05, `a183083`)

Of ~26 s on this input (3.8e11 insts), ~21.5 s is **liveness**, not region
allocation. A separate superlinearity from the splitting ones. It is
`heavy/01` in `compilation-speedup-002`'s sets, and is now the
second-heaviest input.

**Status:** **fixed** by `compile-speedups-005` (`a9dc9c1`), which found the
cause and closed it: **the worklist was a LIFO `Vec`**. It was *seeded* in
post-order, which is right for a backwards analysis, but the first
re-enqueue broke that order, and this input's switch dispatch has **4,097
successors**, so it was re-enqueued and re-popped after nearly every arm --
**4.54 visits per block, ~16,400 visits of that one block**, each
re-running `transfer_edges` over all 4,097 successors and almost always
learning nothing (134M `SortedVec` unions).

A `BinaryHeap` keyed by reverse post-order index keeps the order after a
re-enqueue too. A monotone fixpoint does not depend on visit order, so the
output is unchanged. **-92.3% insts and -83.3% wall on this input**, ~0% on
ordinary functions.

This is the same pathology `compile-speedups-004` fixed in redundant-move
elimination, which had been left in place here. **Check every fixpoint's
visits-per-block, not just the one a previous session fixed.**

## Tooling facts (2026-10-05)

- **`timing.rs`'s "ms" was wrong before 2026-10-05**: it printed
  `as_millis() + as_micros() * 1000.0`, i.e. ≈ µs × 1000. Fixed to
  `as_secs_f64() * 1000.0` with three decimals. Timing logs from before the
  fix (including any in older reports) need dividing by ~10⁶.
- **`run` links regicide with `visualizer`, `trace-log`, `timing`, and
  `checker`**, through `[dev-dependencies]`. Rebuilding with only `std`
  (in a scratch copy) changed instructions by about −0.3% on one input, so
  the `run` numbers are representative, but event construction is in them
  and not in production.
- `insts-retired` noise: CV ≈ 0.1% on `corpus-keccak` (68 inputs, 2.3·10⁹
  insts per sample). Wall-time CV on the same set: ~24% at 0.3 s per sample,
  so small sets need many samples, or a heavier set, to resolve wall time.
- Replaying a whole corpus in one process can take hours (`corpus-sqlite3`
  alone is >10⁴ seconds, nearly all of it in a handful of inputs). Its
  stdout is buffered, so it shows no progress and looks hung. Use the census.
- An apparent "hang" of `tinygo-regex-0060` (4.5KB, 5·10⁶ insts alone) was
  in fact the *previous* input, `tinygo-regex-0047`, still running: `run`
  prints the `===` header and then allocates, all in a `BufWriter`. Do not
  bisect "context pollution" before timing each input alone; one session
  wasted time doing exactly that.
- Disassembly: on macOS, `objdump --source` only finds line info through a
  dSYM. `scripts/disasm.sh` runs `dsymutil` for you. Building with
  `split-debuginfo="packed"` fails here and leaves stray `.rcgu.o` files.
- **Missing tools (2026-10-09):** `samply`, `samply-text` and `rustfilt`
  are **not installed** on this host, so the SKILL's profiling recipe and
  `scripts/disasm.sh` both fail. `cargo fuzz` was missing too until the
  user installed it mid-session. `/usr/bin/sample` and `objdump
  --disassemble-symbols` are the fallbacks; see SKILL.md, "Which
  functions". Check with `which samply samply-text rustfilt` during setup
  rather than discovering each one when you need it.
- `insts-retired` CV on `codegen-analysis-008`'s `typical/` (13,922 inputs,
  ~2e11 insts per sample) is **0.01-0.04%**, and wall CV is 1-4% on a quiet
  host. Both resolve easily at n=12; the host's load is what decides
  whether wall resolves, not the sample count.
- The baseline `cargo test --all-features` at `e53b573`: 389 + 8 passed,
  10 ignored, exit 0, about 2 minutes. At `645db2b`: 402 + 8 passed, 10
  ignored.

## Session `compile-speedups-004` (2026-10-08, base `cf70ddd`, tip `2bac3d3`)

Corpora `codegen-analysis-006` (keccak, sqlite3, tinygo-regex; 3,849
inputs, 2,666 distinct under 1e10 insts). Only two heavy inputs, each
~1e10 insts and ~1 s: `tinygo-regex-0117` and `-0188`. Fifteen attempts,
fourteen kept, all output-identical. Cumulative, n=30 / n=10, load 3-5:
`typical/` -47.9% insts, -40.3% wall (7.26 s -> 4.33 s); heavy/00 -58.8%
wall; heavy/01 -48.8% wall. Report: `reports/compilation-speedup-004/`.

What worked, largest first (typical insts):

| change | typical | where |
| --- | ---: | --- |
| RME fixpoint worklist in RPO instead of LIFO (4.8 visits/block -> ~1) | -17.5% | `redundant_move_elimination.rs` |
| Per-unit assignment/reservation maps: sorted `Vec`, not `BTreeMap` | -12.1% | `region_allocation/assignments.rs` (`UnitMap`) |
| Liveness value sets: sorted `Vec` with merge-based `union_with` | -9.0% | `btree.rs` |
| Retire split candidates whose prefix already exceeds the best score's interference | -7.6% | `splitting.rs` (`Beaten`) |
| Retire split candidates whose prefix went infinite | -5.1% | `splitting.rs` |
| Prune split suffixes against the best of *all* cuts so far | -3.8% | `splitting.rs` (`floor`) |
| Check where the last register candidate was blocked first (assignment, eviction) | -1.3% each | `assignments.rs` |
| Counting sort of non-preferred candidates; usable-hint count as a subset test; constraint computed once; packed `u128` span sort keys; rotate instead of splice in `fill_row` | -0.35% to -1% each | various |

What lost or did nothing (screened or measured):

- Galloping / "search near the last hit" in `UnitMap` (+0.9% and +2.4%,
  two designs): 98% of consecutive searches land within one entry, but a
  binary search over a few hundred entries is ~8 steps and threading a
  cursor costs more.
- Pricing the suffix first when it was infinite at the last cut: +5.4%;
  it loses the prefix-first prune.
- Keeping per-unit `Vec` capacity across `Assignments::reset` by walking
  every unit: neutral.
- Packed sort key for `resolve`'s `(HalfMoveKey, Allocation)`: +0.4%; the
  keys are already inline.
- Skipping the per-edge RME state copy on edges with nothing to apply:
  neutral once the worklist was fixed.
- Reordering the overlap and kind tests in `regs_clobbered_across`:
  neutral (85% of spans are in blocks with no reservations).

**Where the time goes at `2bac3d3`** (`typical/`): region allocate 46%,
generate moves 13%, coalesce 13%, live ranges 8%, RME 8%, liveness 2.6%.
samply: `split_between_spans` (u16) 19.7%, of which
`SpanInterference::weight` 13.3% and `fill_row` 9.5%; `generate_moves`
7.5%; `assign_via_eviction` 4.6%.

**Status:** open. `fill_row` is the top item: 1.67M rows and 32M binary
searches on `typical/`. Ruled out: lazy filling (96% of a row is read),
reuse across splits (7% of rows), faster searches (above), direct queries
for once-read rows (13% of rows, 5% of queries). Untried: a per-unit,
per-block summary that lets a query skip units with nothing assigned in the
span's block. Also open: eviction probes blocked by a second bundle (not a
reservation) could use attempt 9's "blocked at" shortcut too.

The baseline `cargo test --all-features` at `cf70ddd`: 421 + 8 passed, 10
ignored. At `2bac3d3`: 424 + 8 passed, 10 ignored.

## Session `compile-speedups-005` (2026-10-09, base `7e8f866`, tip `757d59f`)

Corpora `codegen-analysis-008` (33,038 inputs across 29 benchmark families,
13,922 distinct under 1e10 insts; 8x broader than 006). Ten attempts, eight
kept, ten more ideas screened out at no attempt cost. Report:
`reports/compilation-speedup-005/`.

Cumulative, n=12/10, 99% CI, significant on both metrics:

| set | insts | wall |
| --- | ---: | ---: |
| `typical/` (13,922) | **-28.43%** | **-19.69%** |
| heavy/00 `starlingmonkey-markdown-15922` | **-56.65%** | **-47.23%** |
| heavy/01 `shootout-switch-0004` | -92.35% | |
| heavy/02 `starlingmonkey-markdown-14982` | -25.14% | |
| heavy/03 `hashset-0004` | -15.35% | |

**Codegen quality improved**: estimated cycles over `typical/` -0.39%,
weighted moves -5.5%.

### The central finding: the cost is an exponent, not a constant

Log-log slope of `insts` against input bytes, per family, over the census:
**every family is 1.5 to 2.2**, none linear. Pooled, median insts/byte rises
70x from the smallest inputs to the largest. Ion is near-linear, so the
compile-time gap widens with function size and is dominated by the largest
functions. Compute this straight from the census TSV; it decides what kind
of change to look for.

### What worked, largest first (typical insts)

| change | typical | where |
| --- | ---: | --- |
| **Cut a between-spans split in the middle instead of searching for it** | **-22.56%** | `region_allocation.rs`, `splitting.rs` (`cut_near_middle`) |
| Fill a split candidate's row in one sweep of the unit's assignments | -2.64% | `assignments.rs` (`fill_row_from_one_unit`) |
| Remove an evicted bundle's assignments from its own units only | -2.26% | `assignments.rs` (`remove_assignment`) |
| Bucket a long span sort by value before sorting | -1.24% | `live_ranges.rs` (`sort_keyed_by_val`) |
| Insert a single interval into a set with a treap insert | -0.59% | `interval_sets.rs` (`insert_one`) |
| Walk to the end of a location's facts instead of searching | -0.43% | `redundant_move_elimination.rs` (`range_of`) |
| Pop liveness's worklist in post-order instead of LIFO | -0.38% | `liveness.rs` -- but **-92% on `shootout-switch-0004`** |
| Remember a bundle's clobbered registers across eviction re-pushes | -0.26% | `region_allocation.rs` -- **-8.3% on `hashset`** |

**The split search was 22% of `typical/` and 51% of the heaviest input.** A
throwaway probe (cut at the midpoint, price nothing) established that before
any real work. The replacement is **not** ion's conflict-derived cut, which
measured **+216%**: the first conflict is nearly always in the bundle's
first span, so cutting there peels one span per split and a long bundle
takes O(spans) splits. Clamping towards the middle fixed it, and sweeping
the clamp showed the conflict contributed nothing -- the shipped version
ignores it. **This one changes the allocation output** (permitted for that
commit only) and improved estimated cycles by 0.39%.

Liveness's LIFO worklist was the same pathology session 004 fixed in RME,
still present: 4.54 visits per block on an input whose switch dispatch has
4,097 successors, re-visiting that block ~16,400 times. Check **every**
fixpoint, not just the one a previous session fixed.

### What lost (screened, no attempt spent)

- Per-unit occupancy bitmap over live points (+6.3%): the per-insert write
  costs more than the 21% of searches it skips.
- Cursor threaded through the general interference query (+5.0%), and
  through a dedicated row-fill query (typical +1.09%). A **null test**
  (cursor present but never firing, still +0.9%) showed the cost was the
  per-span call chain, not the search -- which is what led to the bulk fill
  that replaced the loop outright.
- Extending the bulk fill to reservation-holding units (+3 to +6%): those
  rows are cheap *because* the per-span path exits at the first reserved
  span. A big fallback share is not automatically opportunity.
- `u32` instead of `usize` for `SpanInterference::prefix` rows: flat.
- Hoisting the "is this unit reserved at all" test out of the span loop:
  flat; the optimizer already did it.
- Skipping `sort_spans` when the list is already sorted: a wash (the
  pre-sorted third are the tiny lists; the big calls are never pre-sorted).
- Scanning instead of binary-searching for the *start* of a location's facts
  in RME: flat on `typical/`, -0.38% on `hashset`. Attempt 3 took the win
  that was there.
- Caching `compute_bundle_priority` like the clobber set: **unsound** --
  priority reads hints, which allocation mutates; it differs on 77% of
  re-pushes.

### Where the time goes at `757d59f` (`typical/`)

region allocate 24%, generate moves 17%, coalesce 17%, live ranges 14%,
RME 11%, everything else 17%. **The profile is flat**: no pass above a
quarter and no function above a few percent. Region allocation was 40% at
the session's start.

**Status:** open, but the easy structural wins are gone -- the last three
attempts were worth ~1% each against 22% and 6% for the first two. Leading
candidates, in order:

1. **Measure where this left regicide against ion.** `codegen-analysis-008`
   had regicide at **+249% geomean**; per-family arithmetic implies roughly
   **+150%** now, with `shootout-switch` (worst at +1,255%) near **+23%**.
   That is arithmetic on two measured columns, **not a measurement** --
   confirm it with the `analyze-regicide-codegen` skill before building on
   it. Regicide does **not** beat ion on compile time yet.
2. Generalize "one merge per (bundle, register)" -- ion's design, and the
   shape of the bulk fill -- to `try_assign` and `try_evict_and_assign`,
   which still query span-by-span. Copy ion's **bounded skip**: step
   forward, and re-seek the tree after 16 steps. All three cursor attempts
   in this repo lacked that, and `for_each_overlapping` is still top-10.
3. Coalescing's multi-run merges: `insert_one` took the 55% of unions that
   add one interval; the rest are genuine merges at ~26 node visits each,
   and coalescing is 17% of `typical/`.
   **-- Still open, and now measured** (`-006`): `check_disjoint` alone is
   **1.7% of `typical/`**, and 62% of its expensive walks are these real
   merges. A singleton fast path was tried and bought nothing (-0.07%).
4. RME's `clobber`: 555k calls on a mixed sample, 75% finding nothing, each
   searching a 14-entry vector. An occupied-location bitmap answers those in
   O(1). Ceiling ~2.6% of `typical/`.
   **-- Tried in `-006` and it lost (+1.9%).** The bitmap's maintenance is
   affordable (+0.33%); the *branch it adds* costs the rest. See that
   session's entry. `clobber` itself is real (~1% of `typical/` by a
   marginal-cost probe), so the cost stands; just not this fix.

The baseline `cargo test --all-features` at `7e8f866`: 428 + 8 passed, 10
ignored. At `757d59f`: 430 + 8.

## Does the replay harness's speedup reach the real compiler? (2026-10-15)

**Partly answered, and the controlled experiment has not been run.**
Analysis 010 measured the whole suite's compilation phase at `da7b1da`
(all three `compile-speedups-006` commits landed) against ion:

| | geomean vs ion, 29 modules |
| --- | ---: |
| analysis 009, at `4fa422a` (before) | **+173%** |
| analysis 010, at `da7b1da` (after) | **+166%** |

Right direction and roughly the right size for a ~2% allocator speedup
diluted across whole-module compilation — **but it is not a controlled
measurement**, and note it predates `compile-speedups-007`'s much larger
-10.24% (see that session below, whose gains are not in these numbers): sightglass was updated between the two runs
(`fc2da43` → `32b5ef2`, which also changed the significance test) and
**both engines were rebuilt**.

Analysis 009 had flagged exactly this gap ("ion was rebuilt too, so part
of that bias may be Cranelift's rather than regicide's — a `build-at`
comparison would separate it, and was not done"). **`scripts/build-at`
is the fix and it is this skill's to run:** build at `231bcdf` and at
`da7b1da`, which differ *only* by these three commits with Wasmtime held
fixed, and time `wasmtime compile` on the same modules. Analysis 010
built those exact two revisions and confirmed they produce identical
code, so the timing would isolate the compile-time change cleanly.

Still slower than ion on **29 of 29** modules at `da7b1da`: `hashset`
+660%, `tinygo-regex` +319%, libsodium ~+275-296%,
`starlingmonkey-markdown` +230%, `rust-wasmprinter` +229%,
`shootout-switch` +65%, `ocaml-raytrace` +64%.

## A third of every corpus capture is a trampoline (2026-10-15)

**Relevant to every census and every "typical/" set this skill builds —
and it applies retroactively**: `compile-speedups-007` established that
the `codegen-analysis-010` corpus is **byte-identical to 009's**, so the
split below describes the corpora sessions 006 and 007 censused too, not
only the newest one.
Analysis 010 decoded the capture-name prefix: `u<N>-<M>` is a Wasmtime
**`FuncKey`** (`wasmtime/crates/environ/src/key.rs`), with a
function-*kind* tag in the top 4 bits and a `StaticModuleIndex` in the
low 28 — **not** a module index, which is what the bit pattern suggests.

Over the 33,038 captures of the `codegen-analysis-010` corpus:

| kind | share |
| --- | ---: |
| `DefinedWasmFunction` | **67.13%** |
| `ArrayToWasmTrampoline` | 28.13% |
| `WasmToArrayTrampoline` | 3.18% |
| `ComponentTrampoline` | 0.82% |
| `WasmToBuiltinTrampoline` | 0.45% |
| `ModuleStartup` + `ResourceDropTrampoline` | 0.28% |

So **32.87% of a corpus is compiler-generated glue** — usually tiny, and
cheap to allocate. This session's `typical/` set was **13,925 distinct
inputs** of 33,038 captures; the de-duplication evidently removes most
of them, but **a census or a per-pass share computed over raw captures
is counting two populations**. Worth splitting by kind before drawing a
scaling exponent or a pass share from one.

## Session `compile-speedups-006` (2026-10-13, base `4fa422a`, tip `1489df3`)

Corpora `codegen-analysis-009` (33,038 inputs; **same file names as 008 but
different contents**, regenerated after block frequencies, remats and lazy
critical-edge splitting, so an older census does not transfer). 13,925
distinct inputs under 1e10 insts, and **only three heavy inputs**, each
about a second. Report: `reports/compilation-speedup-006/`.

Three attempts, three kept; **ten further ideas screened out at no attempt
cost**. Cumulative, n=12/10, 99% CI, all significant, **no regression on any
set**, allocation output **byte-identical** everywhere (the session's
permission to change output was never needed):

> **The byte-identical claim was independently confirmed on 2026-10-15**
> by `analyze-regicide-codegen` analysis 010
> (`~/regalloc2/reports/codegen-analysis-010/bisect/experiment-2-compile-time-commits.md`).
> Instead of replaying a corpus, it built a **real Wasmtime** at
> `231bcdf` (before these three commits) and at `da7b1da` (after) and
> compared the compiled artifacts: **0 of 4,890 functions differ across
> six modules, and all six `.cwasm`s are byte-identical by `md5`.**
> That is stricter than a function comparison and independent of this
> session's own harness, so the claim holds through the whole
> Cranelift pipeline, not just through `examples/run`.
>
> **Caveat on reach:** six modules, chosen as that analysis's targets,
> including the two largest and most allocation-stressing of the timed
> set (`dotnet-raytracer`, `tinygo-regex`). The other 23 were not
> checked.

| set | insts | wall |
| --- | ---: | ---: |
| `typical/` (13,925) | **-2.09%** | **-2.32%** |
| heavy/00 `starlingmonkey-markdown-15922` | -1.97% | -1.56% |
| heavy/01 `starlingmonkey-markdown-14982` | -1.25% | (n.s.) |
| heavy/02 `hashset-0004` | -0.23% | (n.s.) |

### What worked

| change | typical | where |
| --- | ---: | --- |
| Index each block's incoming edges instead of two binary searches per live-in span (208k calls for 1.35 edges each) | -0.91% | `move_generation.rs` |
| Compute each edge's move position once (recomputed 10.7x per edge) | -0.69% | `move_generation.rs` |
| **Delete RME's `State::kill`**, a `retain` that removed **0 facts in 120,197 calls** | -0.53% | `redundant_move_elimination.rs` |

The third is the one to copy the *method* from: `kill` scanned every fact
to forget the value being defined, but the preceding `clobber` already took
that definition's own locations and **by SSA nothing else can hold a value
only now being produced**. It became a `debug_assert`, which 593k fuzz runs
and the full suite then checked. Output byte-identical.

### What lost (ten screens, none costing an attempt)

Three were sizable regressions, caught before any attempt was spent:

- **Occupancy bitmap in front of RME's `clobber`** (+1.9%): 73% of calls
  find nothing, but the null test put maintenance at only +0.33%, so **the
  fast path itself cost ~1.5%**: a 27/73 data-dependent branch in front of
  a `partition_point` over 13.5 cached entries. (`hashset`, whose lists are
  far longer, went -0.6%; everything else regressed.) This is `-005`'s
  occupancy-bitmap finding in a second pass.
- **Merging a bundle's whole span run into a unit at once** (+2.6% typical,
  **+14.7% on `hashset`**): 16.6M element shifts would have become ~4M, but
  the null test put the scaffolding at +0.15%, so the merge itself was the
  regression. One `memmove` of 57 elements beats 57 individual swaps.
- **Packed `u128` sort key for `resolve`'s `dests`** (+0.24%): `-004`'s
  "packing loses when the key is already inline" in a new place.

Flat or too small: bucketing DME's operands by `(position, kind)` (-0.10%,
though 75% of its 1.5M operand visits are "wasted"); raising coalescing's
fuel x4/x8/x16 (~0%, the budget never binds); hoisting the edge load out of
the live-in loop (the optimizer already did it); skipping
`sequentialize_batch`'s sort when presorted (batches average 7.4 moves); a
singleton fast path through `check_disjoint` (-0.07%, see below).

**Deliberately not attempted:** `sequentialize_batch`'s `dedup_by_key`
removes **0 of 9.26M** expanded moves over the whole corpus, but unlike
`kill` nothing *guarantees* it cannot fire, since two group moves in one
batch
can legitimately expand to the same `(src, dst)` pair. The corpora simply
lack that shape.

### Scaling: the exponent is spread across every pass

Pooled log-log slope of insts against bytes over the new census: **1.72**
(per family 1.45 to 3.24). Bucketing `dotnet-raytracer` geometrically by
size and timing each pass per bucket gives each pass its own exponent:

| pass | slope | share of the largest bucket |
| --- | ---: | ---: |
| coalesce | **1.85** | 22.6% |
| generate moves | 1.79 | 20.5% |
| region allocate | 1.68 | 33.1% |
| eliminate redundant moves | 1.66 | 13.1% |
| live ranges | 1.47 | 10.7% |

**No pass carries the superlinearity alone**, which correctly predicted that
no single structural fix was available this session.

- **Coalescing's superlinearity is intrinsic**: affinities are
  `edges x live-in set per edge`, and **95.6% of the live-in spans scanned
  produce an affinity**. Live-in set per edge grew 10.9x while bytes grew
  32x. Not waste.
- **Coalescing pays for itself many times over**: refusing every merge
  (ceiling probe) made the rest of compilation **+51% on `typical/` and
  +212% on `hashset`**. Do not look for ways to do less of it.
- **All three dataflow fixpoints are correctly ordered now** (liveness
  post-order, RME and DME reverse post-order). Visits per block still rise
  with input size, 1.01 at the smallest bucket to 2.0-2.7 at the largest,
  but that is **genuine convergence, not the LIFO bug** of `-004` and
  `-005`, which showed as a flat ~4.8 at every size.

### Where the time goes at `1489df3`

The profile is **flat**: the largest self-time row in the whole process is
4.1%, and `generate_moves` (13%) is the only item above 10%. On a sample:
`generate_moves` 12.2%, RME `analyze` 7.6%, `coalesce_affinity` 6.4%,
`assign_via_eviction` 5.3%, `assign_to_non_preferred` 5.3%,
`allocate_region` 5.2%, RME `rewrite` 3.8%, `split_between_spans` 2.9%.

Move generation's sub-passes (instrument `enter_pass`): **`EmitHalfMoves`
58%**, `Sequentialize` 18%, `Resolve` 17%, `EmitReservationHalfMoves` 6%.

**Status:** open. Leading candidates, with measured ceilings:

1. **Coalescing's genuine multi-interval merges.** A marginal-cost probe
   puts `IntervalSet::check_disjoint` at **1.7% of `typical/`, 2.2% of
   heavy/00**, the largest single target found. 59% of its calls fall
   into the interleaving walk, and **62% of those are real multi-interval
   merges**, so a singleton fast path does not help (measured: -0.07%).
   Needs a better merge over the treaps. This is `-005`'s item 3, now with
   a number.
2. **The ~8% around `emit_dest`.** Ceiling probes: deleting the live-in
   edge loop is -10.2%, and `black_box`-ing only its `emit_dest` calls is
   -8.3%, so ~2% is walking edges and ~8% is recording destinations and
   what `resolve`/`sequentialize` do with them. Emitting one dest per span
   instead of per edge bounds the fan-out at -2.05%, but each edge
   genuinely needs its own move. `resolve`'s sort is 0.88%; its hash lookup
   is only 0.14%. The `sources` map is read *during* `emit_half_moves`
   (`arrives_in_the_gap`), so it cannot simply become a merge join;
   splitting its mid-pass role from its post-pass role is the way in.
3. `MoveGeneration::spans_range` still has the two-binary-search shape
   attempt 1 removed from `incoming_edges`, over `self.spans` keyed by
   value.
4. `UnitMap::merge` uses the swap-based merge that lost badly to
   `Vec::insert`'s `memmove` above; check whether it should change.

`-005`'s item 1 (measure regicide against ion) and item 2 (bounded-skip
cursors in `try_assign`) were **not** attempted here and remain open.

The baseline `cargo test --all-features` at `4fa422a`: **431 + 8 passed, 10
ignored**, exit 0, ~100 s. Unchanged at `1489df3`.

## Session `compile-speedups-007` (2026-10-15, base `da7b1da`, tip `157ff2d`)

Corpora `codegen-analysis-010` -- **byte-identical to `009`'s** (same
33,038 files; 41 sampled files all `cmp`-equal, the only difference a new
`README.md`), so that session's structural findings carry over, but the
tree was 2% faster so the census was re-run. Same shape as before: 13,925
distinct inputs under 1e10 insts and three heavy inputs of about a second.

Five attempts, **four kept**; three further ideas screened out and six
probes run. Cumulative, n=12, 99% CI, **all significant on both metrics**,
no regression on any set, allocation output **byte-identical everywhere**
(the session had no permission to change it and never needed any):

| set | insts | wall |
| --- | ---: | ---: |
| `typical/` (13,925) | **-10.24%** | **-7.96%** |
| heavy/00 `starlingmonkey-markdown-15922` | **-29.12%** | **-24.52%** |
| heavy/01 `starlingmonkey-markdown-14982` | -9.84% | -12.22% |
| heavy/02 `hashset-0004` | -1.59% | -2.43% |

### What worked

| change | typical | where |
| --- | ---: | --- |
| **`SecondaryMap::index_mut` grows with `resize`, not a `push` loop** | **-8.68%** (heavy/00 **-28.10%**) | `entity/map.rs` |
| Order a register class by tier once per region, not per bundle (97.4% hit) | -0.89% | `region_allocation.rs` |
| Span hints held out of line: `LiveSpanData` 144 B -> **16 B** | -0.60% insts, **-2.91% wall** (heavy/00 **-16.12% wall**) | `live_ranges.rs` |
| Delete `last_ending_by`'s `next` pre-walk; descend the treap directly | -0.22% | `interval_sets.rs` |

**The first is the headline and the lesson.** It is one line in a shared
container, not in any pass: `index_mut` materialized the defaults between
its length and the key one `push` at a time. Six sessions walked past it
because the profile names `push_mut<Option<LiveSpan<u32>>>` and `capacity`,
never a pass. **When a flat profile's biggest self-time rows are container
internals, read `entity/`.**

### Probes, and what they ranked

Every attempt this session was chosen by a marginal-cost probe first:

| probe | typical | outcome |
| --- | ---: | --- |
| `reuse_aware_constraint` called twice | **+3.53%** | largest target found; **still open** |
| `check_disjoint` called twice | +1.71% (heavy/00 +2.97%) | drove the treap attempt |
| `order_non_preferred_candidates`' two scans | +1.53% | drove the tier-order attempt |
| +128 B dead padding on `LiveSpanData` | +1.36% | drove the span-shrinking attempt |
| +192 B dead padding on `LiveBundleData` | +0.13% | **rejected**: 10x less, despite being the larger struct |
| `is_live_in` called twice | +0.12% | rejected: 99.998% true but no invariant makes it so |
| `spans_range` searched twice | -0.18% (noise) | rejected: `-006`'s open item 3 is **not** worth doing -- 5,459 calls, not 208k like `incoming_edges` |

**Padding probes rank shrink candidates in minutes**, and ranked these two
10:1 the opposite way round from how they look. `RegSet` is **64 bytes on
every machine** (`Reg::MAX = 512`, while the corpora's machines define 128),
so grep hot structs for it.

### What lost

- **A linear fast path in front of a search, for the fourth time.**
  `last_ending_by`'s `next` walk averaged 2.03 steps and *still* descended
  24.2% of the time. A sweep over 0,1,2,3,4,6,8,12,16 was **monotone in
  favor of 0**. Joins `-005`'s and `-006`'s bitmaps and the three cursors.
- **Guarding `is_reuse_target`'s scan by operand kind** screened at -0.92%
  with **byte-identical output on 600 inputs** -- and was wrong:
  `validation.rs` requires a `Reuse`'s target to be an early *use*, so
  `kind() == Def` skipped exactly the operands that should enter. Corrected
  to `Use && Early`, worth 0.08%. **Identical output means the corpus did
  not notice, not that the invariant holds.**
- Narrowing `param_of`'s index to `u16` (7.4% of values are parameters, max
  index 11): flat at -0.01%. One entry per value is too small a map.
- One node lookup per interval-set loop iteration: -0.10%, and the
  `last_ending_by` half added nothing, so the optimizer already had it.

### Verification findings

**Two of four kept attempts had mutations that passed everything.** Both
needed more than the default recipe:

- The tier-order cache: dropping the `region_preferences` invalidation
  passed the full suite *and* left output byte-identical on 600 typical
  inputs and two heavy ones, because that case is **27 of 66,885 asks
  (0.04%)**. Fixed with a `#[cfg(debug_assertions)]` block that rebuilds
  the order and compares; the same mutation then fails immediately across
  many tests. **Any cache whose staleness window is rarer than ~1% should
  carry one.**
- The split-hint handoff: reversing which half keeps which hint also passed
  everything with identical output (the hint only biases a preference later
  allocation usually overrides). Fixed by extending the existing
  `split_bundle_within_span` property test.

A **false fuzz crash** recurred exactly as SKILL.md warns: a screen written
into `src/interval_sets.rs` during the fuzz *build* produced a panic at
1,024 execs that did not reproduce at the commit; a clean re-run did 424k
runs green.

### Fixpoints: all three still correctly ordered

Visits per block -- liveness 1.49 (small sample) to **5.18** (heavy/01),
RME 1.17-2.28, DME 1.24-3.27. Liveness near 5 looks like `-004`/`-005`'s
LIFO signature but is **not**: the pop order is a max-heap on RPO index
(post-order, right for a backwards analysis) and the figure **rises with
input size**, which is genuine convergence. The bug shows as a *flat* ~4.8.

### Where the time goes at `157ff2d` (`typical/`, timing log)

region allocate 26.7%, coalesce 16.8%, generate moves 16.5%, live ranges
11.8%, RME 10.1%, DME 4.3%, liveness 3.3%, everything else 10.5%. Almost
unchanged in *share* from `-006`, because the two largest wins were spread
across every pass rather than concentrated in one.

**Status:** open. Ranked candidates:

1. **`reuse_aware_constraint`, +3.53% by probe** -- the best-measured
   target left. 1.06M calls at **5.38 per distinct `(inst, operand)`**, so
   82% are recomputation across passes. Only 3.1% find a reuse tie, and the
   sibling scan is 0.06 operand visits per call, so the cost is
   `is_reuse_target` scanning every operand on every call. Cannot be
   skipped by operand kind (see above). A memo keyed by `(inst, operand)`,
   or folding the constraint into `UseData` where the callers go through
   `Use`, is the way; note `Use::is_fixed`'s doc explicitly says it uses
   "nothing cached", so check why before changing that path.
2. `resolve`'s `dests` sort: **1.2%** by probe (sort, reverse, re-sort --
   no clone). `dedup` removes only 0.1% of 309k entries but cannot go,
   since two group moves can legitimately expand to one pair.
3. `check_disjoint`'s remaining ~1.5%: 2.22 loop iterations per walk, and
   `-006` showed 62% are genuine multi-interval merges, so this needs a
   better merge, not a fast path.
4. `-005`'s item 2 (bounded-skip cursors in `try_assign`) and item 1
   (measure against ion) remain untried across three sessions now.

The baseline `cargo test --all-features` at `da7b1da`: **433 + 8 passed, 10
ignored**, exit 0, ~100 s. At `157ff2d`: **433 + 8** (two tests extended,
none added).

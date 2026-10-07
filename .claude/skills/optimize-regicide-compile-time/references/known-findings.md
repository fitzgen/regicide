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

**Status:** open. Ideas not yet tried, ranked:

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

**Status:** open, not profiled.

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
- The baseline `cargo test --all-features` at `e53b573`: 389 + 8 passed,
  10 ignored, exit 0, about 2 minutes. At `645db2b`: 402 + 8 passed, 10
  ignored.

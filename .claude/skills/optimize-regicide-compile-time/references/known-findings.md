# Known findings

What earlier sessions established about where regicide's compile time goes.
Each item has the date, the sha it was measured at, and its status. Re-verify
anything you are going to build on: regicide changes quickly, and a finding
can be fixed by someone else between sessions. Add to this file (via
`misc/skill-learnings.md`, for the user to fold in) whenever a session
learns something durable.

## The workload is extremely skewed (2026-10-05, `e53b573`)

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

**Status:** open. Nobody has yet established *which* quantity the heavy inputs
are superlinear in (values, blocks, regions, bundles, splits).

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

**Status:** open. Not yet checked whether the heavy inputs have the same
profile (likely, but verify), or what `typical/` looks like.

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
  10 ignored, exit 0, about 2 minutes.

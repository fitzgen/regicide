# Known findings

What earlier sessions and analyses established that matters for improving
regicide's code quality. Each item has a date, the sha it was measured at, and
its status. **Re-verify anything you build on**: regicide changes quickly, the
user works on it in parallel branches, and a finding can be fixed between
sessions. Propose additions via `misc/skill-learnings.md`, for the user to fold
in.

Deltas follow the analysis skill's convention: (regicide - ion) / ion, so
**negative is better**.

## Latest session: `code-quality-001` (2026-10-06, base `bf6be7d`)

`reports/code-quality-001/report.md` in the `regicide-codegen-improvements`
worktree (`reports/` is gitignored, so it exists only there). Three attempts
against analysis 003. Whether its kept change landed, and under which sha,
is for you to check: it was left **unstaged** on branch `code-quality-001`,
because `git commit` was refused. Look for "spill a bundle with no uses
whole" in `git log`, or `has_nothing_to_split_for` in
`src/region_allocation.rs`.

| # | idea | verdict | result |
| --- | --- | --- | --- |
| 1 | non-preferred order: grow the function's register footprint in class order (fix #3) | dropped | siphashx24 x19/x20 gone, but keccak guard +0.14% and blake3 corpus +1.97%: unhinted bundles took other bundles' hinted registers inside the footprint |
| 2 | a bundle with no uses and constraint `Any` skips splitting and goes to the stack whole (fix #1) | **kept** | countMatches -48.9%, machine.add -46.4%, VDBE -37.7%; corpora sqlite3 -46.7%, tinygo-regex -59.0%, hashset -40.6%, protobuf -29.8%; guards unchanged; compile time -21.6%; 445 better / 58 worse |
| 3 | keep runs of unused spans together in `split_into_minimal_or_spill` | dropped | no effect on any target: after #2 the shredding is in `split_between_spans` |

If #2 landed, the 003 rankings below are stale for #1 and #4. countMatches'
hot latch went from 12 reloads to 0. Latch reloads over all 29
countMatches loops went 410 → 211. machine.add moves 1,013 → 163. Re-measure
before working on them. What 001 left open, ranked:

1. **Seam loop depth in `SplitScore`** (finding #2). The remaining
   countMatches seams are on depth-4 latches (block1219's six latches, 2-5
   reloads each) and reload values the loop *does* use. `SplitScore` does
   not see the weight of the block a cut's seam lands in.
2. **`hashset-0004-u0-3` regressed +3.3% under #2**: in one 7,442-instruction
   block, v126 (3,419 uses) lost callee-saved r17 and is reloaded 3,368
   times. Why does a bundle that heavy lose its register?
3. **Callee-saved as a `Machine` property** (fix #3). regicide's `Machine`
   has only an order, so "is callee-saved" can only be guessed (003's probe
   hard-coded index >= 16). regalloc2 knows it (`non_preferred_regs_by_class`).
   Adding it is an **API change: ask the user first.**
4. **Depth-0 reload-for-move trades** (most of #2's 58 regressions are
   small): a zero-use bundle that could ride in a free register between two
   uses in straight-line code now reloads. Try restricting #2 to bundles in a
   loop region, or across a call.

## Cold regions and cold-edge spills: `code-quality-003` (2026-10-07, landed as `f12e432`)

`reports/code-quality-003/` in the `regicide-cold-blocks-as-own-regions`
worktree. A user-directed task, not one of 003's findings. Base `bf6be7d`;
landed together as `f12e432` ("Put cold blocks in their own regions; don't
hoist spills out of cold blocks").

| # | idea | verdict | result vs `bf6be7d` |
| --- | --- | --- | --- |
| 1 | split each region's cold blocks into a cold child region, allocated after every other region; no hints from cold to non-cold regions | **kept** | countMatches -1.20%, VDBE -0.06%; cold moves -45% to -65% in every corpus; better 350 / worse 20 |
| 2 | in cold regions, priority tier for values with no spill slot yet | dropped | fixed #1's regressions, but countMatches +1.85%: a value with a slot can still arrive in a register |
| 3 | same tier, keyed on "arrives in a register" | dropped at screen | marks ~20 of 26 cold bundles, so reorders nothing |
| 4 | spill placement never climbs from a block into a more frequent sole predecessor; the store goes on that edge instead | **kept** | removes #1's regressions; cumulative better 372 / worse 1, guards unchanged, compile time -0.22% |

What the code does now, and what to know before changing it:

- **Region tree.** `RegionTree::is_cold(region)`; `Region::loop_region`
  looks through a cold region to its loop. `Output::loop_depth`, spill
  placement's loop guard, and property tests all use `loop_region`. A cold
  block that names its own region (a cold loop header) stays put, so cold
  loops are not separated.
- **Spill placement is frequency-aware, not cold-aware.** Every check compares
  `Block::frequency(func)`: the walk stops at a block whose sole predecessor
  runs more often (`is_edge_spill_block`), the push-up stops before a more
  frequent parent, and a value's stack blocks are placed most frequent first.
  Cranelift sends only COLD or NORMAL today, so graded frequencies are
  untested on real inputs. `a_spill_for_a_less_frequent_read_stays_on_the_edge`
  covers HOT->NORMAL and 10->0.5.
- **An edge store is skipped when the store above would cover another site**
  (`store_above_covers_another_site`). Without it: 13 functions worse, 0
  better. Redundant-move elimination cannot recover these, because it only
  removes a store dominated by an earlier one, and edge stores sit on sibling
  paths.
- **`SpillSite::block()`** is the block the store runs in. For an edge store,
  its `span()` is the predecessor's live-out span, so never derive the block
  from the span.

Open, ranked:

1. **countMatches swings ±2% on tiny upstream changes**, through slot
   assignment and redundant-move elimination, with no hot operand moving
   (stack-to-stack reload/spill pairs 840 vs 919). A lead for #1/#2 below.
2. **Cold loops** (a cold block heading its own region) stay in their region.
   Check breadth before trying.

## Where to start: `codegen-analysis-003` (2026-10-06, regicide `e9b676b`)

`~/regalloc2/reports/codegen-analysis-003/report.md`. On cycles, only one
benchmark resolves as a regression: **tinygo-regex, +48%**. Everything else
is within noise on wall time, though instruction counts are still +5% to +19%
on sqlite3, keccak, siphashx24 and blake3. Since then, `36e91a7` ("Relay hints
across sibling regions") landed; check what it changed on the targets below
before attributing anything.

### Hot functions and their corpus inputs

| benchmark | function | input | corpus |
| --- | --- | --- | --- |
| tinygo-regex | `main.countMatches` | `tinygo-regex-0107-u0-99` | **002**'s `corpus-tinygo-regex` |
| tinygo-regex | `(*regexp.machine).add` | `tinygo-regex-0241-u0-229` | 002's |
| sqlite3 | `sqlite3VdbeExec` | `sqlite3-0226-u0-181` | **002**'s `corpus-sqlite3` |
| siphashx24 | SipHash-2-4 core | `libsodium-siphashx24-0044-u0-34` | 003 |
| siphashx24 | caller (bench loop) | `libsodium-siphashx24-0106-u0-87` | 003 |
| keccak | `keccak_core` | `shootout-keccak-0005-u0-4` | 003 |
| blake3 | `compress_in_place` | `blake3-scalar-0032-u0-22` | 003 |
| hashset | `HashTable::add` | `hashset-0006-u0-5` | 003 |
| hashset | `HashTable::rehash` | `hashset-0009-u0-8` | 003 |
| rust-protobuf | `encode_varint` | `rust-protobuf-0039-u0-31` | 003 |
| switch | hot `br_table` fn | `shootout-switch-0004-u0-3` | 003 |

Corpus `u0-N` is not disassembly `function[N]`: each report states the import
offset (sqlite3 10, tinygo-regex 15, siphashx24 14).

**Compile cost of these inputs**: `tinygo-regex-0107` took ~486 s and
`sqlite3-0226` ~508 s at `e53b573`; 003 measured the VDBE function at ~59 s
after `a183083`/`1f98a23`. Several other tinygo-regex inputs take minutes.
Use `counts.py --only` on them during screening, and expect the full 002
tinygo-regex and sqlite3 corpora to dominate `counts.py`'s wall time.

### Things to fix (003's ranking)

1. **Back-edge reload seams.** A value live through a loop but used in few of
   its blocks is split at the loop head. The piece through the head gets a
   register and the inner pieces spill, so every iteration reloads it on the
   back edge. tinygo `countMatches`' innermost loop has 12 reloads on the back
   edge of a 7-instruction body (ion: 2 loads, 1 store); sqlite3's VDBE has 7
   spills at the head and reloads at the 188-predecessor latch. **This is the
   only cycles regression that resolves (+48%).** Where:
   `region_allocation/splitting.rs` (where the cut lands) and
   `spill_placement.rs` (its loop guard covers spills, not reload seams).
   Status: **largely fixed by code-quality-001 #2**, if it landed. The real
   mechanism, re-derived on `sqlite3-1347-u0-1026`: the reloaded values have
   *no uses* in the loop. Their zero-use bundles were split per block, the
   header and latch pieces were minimal and so won registers (evicting
   non-minimal bundles in a cascade), and the body piece spilled.
2. **Split scoring cannot tell cuts apart.** `interference_weight` charges a
   conflicting bundle's full weight to any half that touches it, so many cuts
   tie. The middle-of-tied-run rule (`a183083`) fixed `machine.add` (99% →
   24% of splits at index 1). It did not fix `countMatches` or the VDBE
   (still 61% at index 1; ~89,000 and ~39,000 pieces to the stack). This is
   the upstream cause of #1. Unverified: that tied runs there are short. A
   scratch counter would confirm it. Status: open.
3. **Callee-saved registers ranked ahead of other bundles' hints.**
   `order_non_preferred_candidates` (`region_allocation.rs`, ~line 1453 at
   `e9b676b`) sorts by `(!clobbered, region_preferences.contains)` above the
   class's own order. So an unhinted bundle takes `x19`/`x20` (a save/restore
   pair) before a caller-saved register another bundle hinted. It hit
   siphashx24's hottest function (`stp/ldp x19, x20` that ion does not need).
   **003 probed a fix**: keep the class's callee-saved tail behind the
   `region_preferences` key. That kept `4aa7bd5`'s move win (19 → 9), dropped
   the save/restore, passed `--check`, and left corpus totals neutral. But
   the probe hard-coded the tail as class index >= 16 (or 24). regicide's
   `Machine` does not know which registers are callee-saved. 001's in-scope
   proxy (rank registers past the furthest one in use last) regressed keccak
   and blake3 and was dropped. The estimate cannot see the prologue
   save/restore, so judge any fix on the register set used, not the estimate
   alone. Status: open, needs an API decision.
4. **`br_table` arms end in register rotations** (9–15 moves per arm to the
   join's assignment). tinygo `machine.add` had 1,013 moves vs ion's 55, and
   sqlite3 VDBE 6,655 vs 640. Caused by between-span split pieces landing in
   different registers per arm (#2), not by `MAX_MERGE_SPANS` any more.
   Status: **largely fixed by code-quality-001 #2** (machine.add 1,013 → 163
   moves): many of those pieces belonged to zero-use bundles.
5. **Register-starved straight-line code** (keccak, blake3): more spills and
   moves than ion, offset in keccak by fewer reloads (remat). No resolvable
   cycles cost. Low priority.

### Clobbers of hinted registers (code-quality-002, 2026-10-06, `bf6be7d`)

`reports/code-quality-002/` in the `regicide-split-at-clobber` worktree.
Three attempts, **all dropped**; tags
`code-quality-002/{split-at-hinted-clobber,clobber-tie-break,per-half-split-candidates}`.
Still valid at `642668d`: `main`'s split-pricing speedups allocate
byte-identically (478 inputs re-checked).

- **The signature is large.** In `assign_to_preferred`, a hinted register
  whose *only* occupants over the bundle are reservations (clobbers, nothing
  evictable) blocks 62,338 failed preferred assignments in hashset, 12,818 in
  siphashx24, 6,681 in switch. Most such bundles go on to
  `split_between_spans` (countMatches 22,332; VDBE 30,580; `hashset-0004-u0-3`
  31,063), then `BundleSpilledToStack`. Probe:
  `misc/probe-clobbered-hints.patch` in that report.
- **The split score is blind to it.** A cut is scored for one candidate as
  `max(I(prefix, c), I(suffix, c))`; a clobber of `c` in either half makes
  that `INFINITY`, so every cut ties for the hinted register.
- **Forcing a cut past the first/last clobber** (overriding the score):
  countMatches +0.91%, VDBE +0.97%, `hashset-0077-u0-72` +6.6%. The cut lands
  deep in loops and the leftover half reloads there.
- **The same cut as a tie-break** among cuts tied for best: **countMatches
  -3.55%** (-740k at depth 4, -292k at depth 3; latch block1368 went
  8 moves + 2 spills + 17 reloads to 7 moves + 14 reloads + 1 remat), but
  VDBE +0.52%, `hashset-0077-u0-72` +7.35%, `tinygo-regex-0156-u0-145`
  +5.61%, typical compile insts +5.8%. A bisection put +339k of `u0-72`'s
  +495k on **one** tie: a 25-span bundle peeled at cut 22 instead of halved
  at 12. **The middle-of-tied-run rule (`a183083`) is load-bearing**; any
  preference that picks a non-middle tie must leave long bundles alone.
- **Scoring each half in its own best register** (`max(min_c I(prefix, c),
  min_c I(suffix, c))`): VDBE -0.99%, rust-protobuf -0.95%, but
  `hashset-0004-u0-3` reloads 10,230 -> 19,957 (+19.9%). Every cut looks
  cheaper and nothing prices the move between differently-aimed halves.
  Needs the seam-move term below first.
- **Next:** the tie-break restricted to cuts near the run's middle or to
  short bundles; or the per-half score plus a seam price.

### Things to preserve (guards)

1. **Treap-based coalescing disjointness** (`efb70f6`). `coalesce-out-of-fuel`
   is 0 everywhere; switch's hot function went 75,737 → 109 moves. Watch the
   `coalesce-out-of-fuel` line in `run`'s output.
2. **Loop-carried values in one register across a nested loop**: hashset
   `rehash` (`hashset-0009-u0-8`), 3 vs ion's 10 moves per outer iteration.
   Relies on inner regions being allocated first and their registers hinted
   up (`hint_across_regions`).
3. **Whole-function coalescing when it fits**: rust-protobuf
   `encode_varint` (`rust-protobuf-0039-u0-31`), 190 merges, 0 refusals, no
   splits, 19 vs ion's 54 moves.
4. **In-loop allocation equal to ion's**: siphashx24's compression loop is an
   identical 34 instructions, and tinygo `countMatches`' counter stays in a
   register.
5. **Remat and small frames**: `keccak_core`, 990 reloads vs ion's 1,112 (190
   remats); frame 336 vs ion's 768 bytes. Make any slot-reuse change
   conditional rather than reverting it.

## Mechanisms and traps from earlier work

- **`SplitScore` does not price the move a cut creates** (2026-10-05,
  hypothesis; 2026-10-06, code-quality-002's per-half-score attempt is
  evidence: it is what sank it). A free cut at a liveness hole and a within-span cut that always
  needs a move score alike. Merging `split_between_spans`/`split_within_span`
  into one best-score phase was neutral to slightly worse, and `keccak_core`
  makes **0** between-span splits, so its in-region moves are not
  block-boundary splitting. A join-point penalty or move-cost term in
  `SplitScore` is the suggested next lever.
- **Lifting a cap can cost compile time** (2026-10-05). Replacing
  `MAX_MERGE_SPANS` made `printf_core` (`shootout-switch-0063-u0-57`) go 35 s
  → 146 s, all in `split_between_spans` → `interference_weight`, because the
  cap had been bounding bundle size. Watch heavy inputs in `diff_counts.py`.
- **Hints: measure width, not hit rate** (2026-10-01). Cross-region hints
  were once whole-class, so "honored" meant nothing.
  `BundleAssignedNonPreferred` with `preference: FixedEntitySet {}` marks an
  unhinted bundle; exclude those from any honor rate.
- **Cold-block trades are intended** (since Wasmtime `00a6476`). Cranelift
  marks sunk blocks `COLD` and coalescing never merges across a cold edge, so
  some moves land in cold blocks on purpose. The estimate weights them 0.05x.
  Since `f12e432` cold blocks are their own regions, allocated last, so a cold
  region cannot evict anything: around a call that clobbers everything, it
  spills whatever does not fit in the callee-saved registers its neighbors
  left free.
- **No loop-depth frequency from Cranelift.** Frequencies are only `COLD` or
  `NORMAL`; loop weighting comes from regicide's region tree
  (`Output::loop_depth`). A loop headed by the entry block is the top-level
  region, so its body counts as depth 0.
- **`critical-edges` is always 0** (Cranelift splits them first), and **move
  elimination is not the limiter**: both passes default to `Global`, so a
  surviving move was created by assignment, splitting or coalescing.
- **Minimal bundles win registers and evict** (2026-10-06, `bf6be7d`).
  `Priority` puts `is_minimal` first and `EvictionCost` ranks a minimal
  victim as more expensive. So a zero-use piece that `split_into_minimal`
  produced outranks and can evict a non-minimal bundle that has uses. That
  cascade is how 003's back-edge seams arose. Any change that creates
  minimal pieces should be checked for it (`BundleEvicted` by a piece with
  `size: 1`).
- **Where splitting happens** (2026-10-06, after 001 #2). In countMatches:
  2,418 `BundleSplitBetweenSpans` vs 122 `BundleSplitIntoMinimal`. A split
  heuristic belongs in `split_between_spans` (one cut at a time, halves
  requeued), not in the minimal split.
- **Event-log traps**: `SpanConstructed` span IDs are provisional (the span
  → value mapping is permuted within a block in the text log; the
  visualizer's data is right). Use the visualizer when you need the value.

## Tooling facts

- `run` prints `estimated-cycles` since 2026-10-06. An older `run` binary
  gives `counts.py` rows with status `no-estimate`; rebuild old revisions
  with the current `examples/run.rs`, `Output::loop_depth`, and the public
  `BlockFrequency::as_f32` patched in, from a `git archive` copy in `/tmp`.
- Byte-identical inputs are common across corpora and reports (shared
  library functions, and corpora re-captured from the same module).
  `counts.py` runs each once: 003's keccak, hashset, siphashx24 and switch
  corpora held 185 distinct inputs.
- Smoke test of the tooling (2026-10-06), `639d9f1` → `36e91a7` on those
  four corpora: hashset -3.53% estimated cycles (reloads +37% in plain
  counts, all on `hashset-0004-u0-3`), keccak -0.48%, siphashx24 +0.24%,
  switch -0.03%; better 19, worse 4. The gate passed. It is a useful example
  of plain counts and estimated cycles disagreeing.
- The baseline `cargo test --all-features` at `36e91a7`: 402 + 8 passed, 10
  ignored, exit 0, about 2 minutes. With 001 #2 it is 403 + 8: the new
  `a_value_unused_in_a_loop_is_not_reloaded_inside_it`.
- **Tests that pinned an allocation shape changed with 001 #2.**
  `a_move_into_a_register_nothing_reads_goes` and the `dead-edits` visualizer
  fixture now use `TestInput::with_a_register_move_overwritten_in_a_later_block`
  (found by a mutatis shrink). `with_a_looping_value_read_only_after_the_loop`
  no longer yields a dead move. Neither the test corpus nor 100,000 mutated
  inputs yielded a dead register move inside a loop under 001 #2.
- **`$S/block_costs.py` + `$S/block-costs.patch`** rank a function's
  estimated-cycles delta by block and loop depth. In code-quality-003 this
  explained every regression in minutes. **The patch builds only on top of a
  tree that builds:** `7d1217e`..`f12e432` (at least) fail to compile with the
  `run` example's features, because `has_nothing_to_split_for`'s early return
  clears a removed `split_span_vals` field. Delete that line in the scratch
  copy (`sed -i '' '/self.split_span_vals.clear();/d' src/region_allocation.rs`)
  until it is fixed.
- **`$S/loops.py`** finds loops, latches and per-block edits in a `run`
  printout. `--latch-reloads N` scans for back-edge seams. At `bf6be7d` it
  found 70 latches with >= 3 reloads in inputs under 5e7 compile insts.
- **Compile insts fell 38% to 92% per corpus at `642668d`**
  (`5e2b0d6`..`645db2b`, split pricing; switch unchanged), with
  byte-identical allocation (`bf6be7d` vs `642668d`, 478 inputs). A
  `counts.py` TSV from before that is fine for estimated cycles but **not**
  as a compile-time baseline: rebuild the baseline at your base.
- **Sensitive canaries for split changes:** `hashset-0077-u0-72` (depth-3
  and depth-4 loops; +5% to +7% under every split change tried in
  code-quality-002) and `hashset-0004-u0-3` (a call-heavy straight-line
  test driver; reloads doubled under per-half scoring). Neither is a hot
  function, so they are not guards, but read them first when a split change
  moves the hashset corpus.

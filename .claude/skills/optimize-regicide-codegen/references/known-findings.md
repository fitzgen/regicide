# Known findings

What earlier sessions and analyses established that matters for improving
regicide's code quality. Each item has a date, the sha it was measured at, and
its status. **Re-verify anything you build on**: regicide changes quickly, the
user works on it in parallel branches, and a finding can be fixed between
sessions. Propose additions via `misc/skill-learnings.md`, for the user to fold
in.

Deltas follow the analysis skill's convention: (regicide - ion) / ion, so
**negative is better**.

> **Read this first: the benchmark suite changed at analysis 008.** Sightglass
> replaced `pca.suite` with **`default.suite`** — 29 modules, up from 17.
> `sqlite3`, `blake3-scalar` and `libsodium-core2` are **gone**; 15 modules are
> new. So every corpus total, guard number and "open, ranked" item recorded
> below for sessions **before** `code-quality-010` refers to a corpus that no
> longer exists, and **none of them is a baseline you can diff against**.
>
> The suite's cost profile also inverted. It is now dominated by
> `dotnet-raytracer` (**6.35G of 7.66G** estimated cycles over 4,153
> functions), whose cost is **49-91% register-register moves at loop depth
> 5-7** — where the old corpus was `countMatches` reloads.
> `starlingmonkey-markdown` is 18,037 of the 33,038 inputs. A session that
> opens by working the pre-008 backlog will optimize the wrong thing: size the
> cost yourself with `edit_costs.py` and `boundary_moves.py` on the heaviest
> inputs before picking a candidate.
>
> **Analysis 009 keeps that suite**, so its corpus is comparable with 008's
> and the warning above still stands for anything older. Its 33,038 captures
> are **13,928 distinct**, and `counts.py -j 12` over them takes about **6
> minutes**, not the ~25 the main skill budgets.

---

> **Correction (2026-10-14): there is no missing callee-saved `Machine`
> API.** Sessions 003, 006, 008/009 and 011 all deferred the callee-saved
> cost model as "needs an API decision — regalloc2 has
> `non_preferred_regs_by_class`, regicide's `Machine` only has an order".
> **The order *is* the answer, and it is strictly more expressive than two
> buckets.** `machine.rs:783-792` documents it ("a class is both the set of
> registers an operand may be assigned to and the order to prefer them in,
> so the caller-saved registers come first"), the captured corpus populates
> it (GPR class: `r0`-`r15` clobbered by ~every call, `r16`-`r25` by none),
> and `order_non_preferred_candidates` already consumes it. 003's
> hard-coded `index >= 16` probe was reading the real convention, not
> guessing — its flaw was hard-coding one class's shape instead of keying
> off the order.
>
> The item persisted because **"callee-saved" was used in two senses**:
> *the callees preserve it* (answered per call site by
> `InputInst::clobbers()`, and genuinely variable — `r2` is clobbered by
> 301 of 533 calls in `rust-wasmprinter-0028`) versus *this function saves
> it* (answered by class order). The backlog item's reasoning ran through
> the first sense while reaching for a mechanism belonging to the second.
>
> **Measured and closed (2026-10-15, code-quality-012 attempt 5, base
> `da7b1da`).** The reuse half of the prescription below was implemented
> exactly as written — a `function_registers: RegSet` outliving the region,
> a 5th tier in `order_non_preferred_candidates` — and judged on the
> register set, as instructed. Over 400 inputs sampled across the corpus:
> **9 functions better, 3 worse, 388 unchanged**, a net of six registers,
> bought with **+0.43% compile time** and +0.64% moves; estimated cycles
> +0.00% with the gate failing on `markdown-16779`. This corroborates
> analysis 010's `callee-saved-survey.md` from the inside: regicide's
> allocation is already near-minimal in registers used, so there is almost
> no headroom. **Do not re-open the reuse bias.** Tag
> `code-quality-012/reuse-registers`.
>
> What that did *not* test, and what remains open, is a **prologue cost
> term** that prices the push/pop pair against the spill it would avoid —
> GCC's `targetm.frame_allocation_cost` (`ira-color.cc:2046`), charged into
> the spill decision and gated on `existing_spills_p`. That is a larger and
> different change: it makes spilling *more* attractive for a function that
> has not spilled yet. Nothing has measured it.
>
> The cost such a term would price: the prologue/epilogue pair is unmodeled
> (`src/` mentions it only in doc comments) and is a *step function* in the
> count of distinct tail registers used (~4.8 per function over the 226
> corpus functions using >= 8 registers). Two constraints any attempt
> inherits: key the model off class order, not observed clobbers (734 corpus
> functions >= 50 insts have *no* clobbering instruction yet use a mean of
> 13.5 registers), and prefer `rust-wasmprinter` over `dotnet-raytracer` as
> the target, which is already -1.06% ahead of ion on wall time. Judge it on
> the register set used, not the estimate; the estimator cannot see a
> prologue. Full write-ups:
> `reports/code-quality-011/misc/callee-saved-api.md` (the correction) and
> `reports/code-quality-012/unsuccessful/05-reuse-committed-registers.md`
> (the measurement) in the `regicide-code-quality` worktree.

## Latest session: `code-quality-012` (2026-10-15, base `da7b1da`)

`reports/code-quality-012/report.md` in the `regicide-code-quality` worktree.
Against **analysis 010** (`~/regalloc2/reports/codegen-analysis-010/`, which
measured **`da7b1da`** — that session's exact base). Branch
`code-quality-012`. Nineteen attempts across two budgets (eleven implemented
and dropped, six rejected by probes); **two kept**.

**Suite estimated cycles -4.82%** (7,220,977,036 -> 6,873,024,304), spills
-2.62%, reloads -2.07%, better 1,405 / worse 1,141, **compile time -0.41%**.
The two kept commits are one change in two halves, both in `Priority`.

| # | idea | verdict | result |
| --- | --- | --- | --- |
| 12 | **a bundle that wants a register queues before one that does not** | **kept** | suite **-4.80%**; raytracer-0385 **-8.73%**, -0386 -8.42%, markdown-16779 -3.72%; compile **-0.43%** |
| 19 | **among bundles a register buys nothing, the small ones first** | **kept** | -0.02%, gate clean; recovers 85% of 12's countMatches cost (+2.02% -> +0.30%) |
| 1 | cap how many times a bundle may be split (`split_fuel`) | dropped | **monotone in the cap**: +0.09% at 3, +0.00% at 10, no-op at 14 |
| 3 | count hints per register, most-asked-for wins | dropped | -0.05%, gate fails; **a count cannot tell a depth-6 border from a depth-5 one** |
| 5 | prefer a register the function already uses | dropped | +0.00%; 9 better / 3 worse over 400 functions (closes open item 1 above) |
| 6 | prefer a cut at a liveness hole | dropped | +0.11% suite, but **xchacha20 -2.44%** — the first in-scope move on it |
| 14 | only a weighted bundle reserves a register | dropped at screen | **+5.78%**, the session's worst: a zero-weight bundle's hint is load-bearing |
| 2, 4, 7, 16, 17, 18 | see the report | rejected or no-op | each closes a line of attack; details there |

What the code does now, and what to know before changing it:

- **`Priority` has a `weight` bit above `size`.** The field order is
  `(is_minimal, group_size, num_hints, weight, size)`, and `weight` is one
  bit: does the bundle have any spill weight at all? One bit rather than
  tiers because the weights do not spread — every nonzero spill weight on
  `dotnet-raytracer-0385` is below 0.5, since `normalize_spill_weight`
  divides a use cost by a length plus 25, and tier bases of 1.5, 2, 4 and 10
  all screen byte-identically.
  - **The size order below it is inverted for zero-weight bundles.** Among
    bundles a register buys nothing, short ones queue first: a long carrier
    holds a register across a wide range, gains nothing by it, and blocks
    every bundle it overlaps. `size` is 22 bits now, down from 23, and a
    bundle over 4,194,303 spans saturates.
  - **Zero spill weight is a superset of `has_nothing_to_split_for`.** It
    also catches a bundle whose uses all price to zero: a non-minimal
    `AlwaysRemat` carrier (`REMAT_ALWAYS_SCALE` is 0.0), and a bundle whose
    uses are all reuse-tied `Any` defs (`use_spill_cost` subtracts
    `MOVE_COST` and floors at zero). Both have uses and something to split
    for, and both are demoted.
- **The queue was the lever, not the boundary.** Four sessions worked hints
  and boundaries on this corpus for tenths of a percent; one bit in the
  queue's sort key was worth -4.80%. Attempt 12's write-up has the probe to
  run before proposing another key: for a candidate, how many comparable
  pairs does it order differently from the status quo? 79-80% there,
  **0%** for attempt 10's (use weight x loop depth), which measured -0.00%.
- **Hint re-ranking within one kind is closed on four independent tries**
  (011's attempts 2, 3, 5 and this session's 3), with the structural
  objection to the first three removed. A fifth attempt needs a difference
  in *kind*. What a count cannot do, and GCC's hard-register cost vector
  can, is weight each border by its frequency (`color_pass`,
  `ira-color.cc:3721`, writing `ALLOCNO_UPDATED_HARD_REG_COSTS`): on
  `-0385` a pure tally traded a real -1.7M at depth 5 for **+6.0M at depth
  6**.
- **`region_preferences` is closed as a decision input** on a fifth and
  sixth try (attempts 14 and 18). Attempt 18 is the sharpest: **0 of 444**
  bundles have an uncontested extra register in their hint union, so there
  is nothing for a preference to pick between.
- **Splitting is not shredding.** Lineages run 11 and 18 cuts deep, and the
  outcome mix *improves* with depth: on `rust-wasmprinter-0028-u0-21`
  unsplit bundles spill 69% of the time while bundles 6-9 cuts deep spill
  ~30%. No finite cap pays. See `$S/split_depth.py`.
- **Open, and the clearest lead: xchacha20's -2.44%.** Attempt 6 is the
  first in-scope change any session has moved the suite's one robust
  wall-time loss with, by trading its depth-2 reloads for register moves. It
  costs the deep-loop targets, and attempt 9 showed a **bundle-depth** gate
  cannot separate them — the cost lands on other bundles at other depths,
  mediated by the register file. Untried: gating on the *function's* shape
  (xchacha20 is depth 1-2 with 93% of its edit cost in stack traffic;
  `-0385` is depth 5-7).

## Previous session: `code-quality-011` (2026-10-13, base `4fa422a`)

`reports/code-quality-011/report.md` in the `regicide-code-quality` worktree.
Against **analysis 009** (`~/regalloc2/reports/codegen-analysis-009/`, which
measured **`4fa422a`** — that session's exact base). Branch
`code-quality-011`, tip **`1902b8a`**. Eight attempts across two budgets
(five implemented, three rejected by probes); **one kept**.

**Suite estimated cycles -3.69%** (7,497,918,888 -> 7,220,977,036 over the
13,928 distinct inputs), better 1,633 / worse 347, compile time +0.90%.
Total *edit* cost fell **29.5%**.

| # | idea | verdict | result |
| --- | --- | --- | --- |
| 1 | **a settled hint outranks a speculative one** (`1902b8a`) | **kept** | suite **-3.69%**; raytracer-0426 -2.44%, -0386 -5.80%, -0385 -5.31%; countMatches -1.33% |
| 2 | among settled hints, follow the majority (tag `code-quality-011/hint-majority`) | dropped | suite **+0.01%**: moves -1.43% bought with spills +0.27%, reloads +0.45% |
| 3 | weigh a settled hint by its border's `Block::weight` (tag `.../hint-weight`) | dropped at screen | targets move *exactly* as in 2; countMatches +1.10%, compile **+3.18%** |
| 4 | revive 010's `stale-region-preferences` by cherry-pick | dropped at screen | **both targets +0.00%**, five guards fail |
| 5 | majority gated to clobber-free bundles (tag `.../clobber-free-majority`) | dropped | **gate passes**, every guard byte-identical, suite still **+0.01%** |
| 6 | reserve a bundle's hint intersection, not its union (tag `.../reserve-intersection`) | dropped at screen | **both targets +0.00%**; countMatches **+4.60%** with every plain count better |
| 7 | the register-pressure case, surveyed | not implemented | five probes, no in-scope lever |
| 8 | repeated argument moves | not implemented | the calls between them clobber `r0-r15`; necessary |

What the code does now, and what to know before changing it:

- **`RegPreference` distinguishes two kinds of hint** (`live_ranges.rs`),
  passed as a `HintStrength`. The *settled* one is the direct branch of
  `hint_across_regions`, where the far side of a border is already assigned.
  The *speculative* ones are the relayed branch, which passes on what another
  neighbor of a still-unassigned far side chose, and the post-split top-ups,
  which hand a piece the parent's whole union.
  - **"Settled" is about reach, not certainty.** `hint_reserved_registers`
    names a register just as committed as a border's, and promoting it was
    measured: **worse on 1,533 inputs against better on 366**, moves +1.50%,
    reloads +0.46%, for +0.009% estimated cycles. A reservation binds a
    register at *one instruction*; a border hint binds one across an edge
    that usually runs many times, so the border is worth more per hint even
    though both name a register that is really there. It stays speculative,
    and a strength named for certainty alone would get this wrong. A settled hint **displaces** speculative
  ones outright; among hints of the same kind, first arrival still wins.
  Pinned by `a_settled_hint_displaces_speculative_ones`. The three existing
  `the_first_hint_*` / `a_later_hint_*` / `a_conflicting_hint_*` tests
  describe the speculative path.
  - **The preference keeps the settled hints' own intersection**, not a
    `bool`, so the rule is a set containment rather than a flag: the
    intersection is always kept within what settled hints allow, and a guess
    may only choose among the registers they leave open. A flag would let a
    guess that merely *narrowed* a wide settled hint mark the preference
    settled, after which a genuinely settled hint naming another register
    would be dropped.
  - **Settledness survives a split.** A span records a bare `RegSet`
    (`hinted_at_start` / `hinted_at_end`) rather than a whole preference,
    because only the direct branch hints a span at all; the relayed branch
    deliberately skips it. `LiveBundle::new` re-folds those as settled, so
    the half it rebuilds ranks hints the way the half rewritten in place
    does. Pinned by `a_rebuilt_preference_keeps_its_hints_settled`. That
    also made `LiveSpanData<u32>` **152 bytes, down from 280**, since a span
    had been carrying two 128-byte preferences whose intersections nothing
    read.
  - The mechanism in one line of allocation diff on the target: the join's
    parameters went from `(r0, r21, r6, r5, r4, r3)` to
    `(r0, r5, r4, r3, r2, r1)`, matching the child loop's
    `(r0, r6, r5, r4, r3, r2, r1)`, so the rotation chains vanished. Three
    depth-6 exit stubs that each emitted the same 8-move rotation became
    **empty**.
  - **Re-ranking hints within one kind is a closed family.** Attempts 2, 3
    and 5 are three independent tries and all land within ±0.01% of flat.
    See the pitfall "Among hints, look for a difference in kind" in
    `SKILL.md`.
- **The `region_preferences` critique is closed from two of its three ends.**
  The set is saturated (79% of the class on `-0385`), stale, *and* ~60% wider
  than needed (mean union 2.26 registers against intersection 1.42). Attempt
  4 fixed the lifetime, attempt 6 the width, and **both left both targets at
  exactly +0.00%**. Displacement is a third source of the staleness that
  neither attempt covered: `push_bundle` folds in a bundle's `union()`, and
  displacing a guess never shrinks that union, so a register that lost a
  displacement contest still deprioritizes itself region-wide for every other
  bundle. Untested, and the two measured ends both came back flat. The saturation was a *symptom* of hints pointing at the
  wrong registers, not an independent defect. Attempt 6 is also the
  session's sharpest counts-vs-estimate case: it gave countMatches 432 fewer
  spills, 407 fewer reloads and 199 fewer moves **and cost it +4.60%**,
  because the freed registers went to shallower blocks.
- **The corpus's cost ceiling.** At `da7b1da`, as a share of the corpus's
  estimated-cycles total: **reg-operands 83.32%**, **reloads 8.48%**, moves
  5.71%, spills 1.93%, remats 0.55%. Five sixths of the metric is
  instructions no allocation decision removes. So eliminating *every* reload
  in the corpus is worth **8.48%**, every move 5.71% and every remat 0.55%.
  Of the **edit cost** alone: **reloads 50.9%, moves 34.2%**, spills 11.6%,
  remats 3.3%.

  **Reloads are the biggest editable class, by ~1.5:1 over moves.** Through
  code-quality-012 this entry and `SKILL.md` both said the reverse (moves
  ~3:1 over reloads, every reload worth 1.70%), because the one-liner that
  produced those numbers summed the printed components raw and `run` prints
  the three stack classes *before* `EstimatedCycles::total` scales them by
  `STACK_COST = 5`. Candidates were sized against the wrong ranking; see
  `SKILL.md`'s cost-ceiling bullet for the corrected command and its
  self-check.
- **The three heaviest inputs are two different problems**, and the same
  change moves them in opposite directions. Together they are ~77% of the
  suite total.
  - `dotnet-raytracer-0426-u0-360` (1.85G) is a **pure boundary** input: 0
    spills, 0 evictions, 0 splits, 89% moves, and `hint_misses.py` reports
    100% "holder took it as its own hint". It responds to hint work.
  - `-0385-u0-321` and `-0386-u0-322` (1.86G each) are **register
    pressure**: 586 of 2,490 bundles spilled, 1,222 split failures, 50%
    reloads, 77% of cost at depth 6. They regressed slightly under every
    attempt that helped `-0426`.
- **`-0385`'s cost is 91% single-instruction edge stubs**, mirrored around
  every deep loop: entry shifts `r17..r22` down by one, exit shifts them
  back up. Five probes ruled out the obvious culprits, and the detail is in
  `reports/code-quality-011/unsuccessful/07-pressure-case-survey.md`:
  - **578 of its 586 spills are zero-use bundles with spill weight exactly
    0.0 and constraint `Any`** going to the stack whole. That is
    `has_nothing_to_split_for` (code-quality-001 #2) working as designed —
    *the spilling is not the problem*. Only 8 spills involve a bundle with
    any use weight.
  - 600 of 877 bundles reaching the eviction step have spill weight exactly
    0.0, so `EvictionCost`'s weight tie-break has nothing to rank with —
    but those are the same zero-use bundles.
  - Coalescing is healthy: 14,240 spans coalesced, **77 refusals, all
    `Overlap`**.
  - 24 identical edit-lists are shared by more than one block, worth 3.36G
    in the estimate — but `block169` and `block172` are on **mutually
    exclusive paths**, so each execution runs one. Code size, not cycles.
    **Do not quote that 3.36G as an opportunity.**
- **Call-argument setup is the biggest remaining move class with a known
  fix.** 15-30% of move cost on the two most move-heavy inputs is moves into
  registers that the next instruction clobbers. `rust-wasmprinter` spends
  **16.9%** of its estimated cycles on moves (the most in the corpus) and is
  **74% interior**, unlike the raytracer's boundary shape. Reducing these is
  analysis 009's **fix #5** — **in scope, no API decision needed**; see the
  correction below.

Open, ranked (measured at `1902b8a`). The session recorded everything here
as out of scope or needing an API decision; **the 2026-10-14 correction
above moved item 1 back into scope**, and it is the best-evidenced one:

1. **A callee-saved cost model** (009 fix #5) — **in scope, needs no API
   decision**, and is the best-evidenced item (see the correction below).
2. **The parent region adopts a child loop's locations** (009 fix #1's
   remainder) — **out of scope** (a new pass). Everything reachable by
   hinting is done.
3. **Is `-0385`/`-0386` worth optimizing at all?** They are ~50% of the
   suite's static cost, but **`dotnet-raytracer` is already -1.06% faster
   than ion on wall time** (robust, 60 samples). 009's fix #5 warns against
   exactly this. Re-justify against wall time first.
4. **Why attempt 5's re-aimed hints help at depth 5 and hurt at depth 6**
   (-1.3M against +6.0M on `-0385`). A localized answer might reopen the
   hint family.
5. **`tinygo-regex-0156-u0-145`** regressed +0.85% under the kept change
   while *every* plain count improved. One spill in one depth-4 block
   (+50,000) against -10,000 each in three depth-3 blocks.

## Earlier session: `code-quality-010` (2026-10-09, base `7e8f866`)

`reports/code-quality-010/report.md` in the `regicide-compile-time` worktree.
Against **analysis 008** (`~/regalloc2/reports/codegen-analysis-008/`, which
measured `7e8f866`, our exact base). Branch `code-quality-010`, tip
`1ec5260`. Five attempts, the user's budget; one kept.

| # | idea | verdict | result vs `7e8f866` |
| --- | --- | --- | --- |
| 1 | count the queued bundles that prefer each register, so a satisfied hint stops reserving it (tag `code-quality-010/stale-region-preferences`, `194a7c3`) | dropped | suite -0.83% but better 873 / worse 3,318, and the whole win is two functions; gate fails on three targets and the siphashx24 guard |
| 2 | **rank a bundle's hints by the weight of their blocks, not how many there are** (`1ec5260`) | **kept** | suite **-1.06%**; raytracer-0386 **-2.97%**, dotnet-raytracer -1.31%; all six guards byte-identical; 201 better / 253 worse; compile time +0.37% |
| 3 | attempt 1 replayed on top of attempt 2 | dropped at screen | raytracer-0386 **+1.66%**, where attempt 1 alone was -2.42% |
| 4 | eviction prices a hint by its blocks' weight too | dropped at screen | no target improved, **compile time +38%** |
| 5 | give the hint rank a fourth bit | dropped | verified no-op: 0 of the 80 heaviest inputs change |

What the code does now, and what to know before changing it:

- **Hint priority saturates** (`region_allocation.rs`).
  `compute_bundle_priority` ranks by `hint_rank(bundle.hinted_span_weight(..))`
  — `Block::weight` summed over the blocks of the spans carrying a usable
  hint, bucketed one tier per factor of ten. It replaced a plain count of
  hinted spans. `region_tree` is threaded into `push_bundle` and the four
  split/evict paths that re-push. Pinned by
  `hint_rank_saturates_past_a_bundles_first_hints`.
  - **What it actually does is saturate the count, not weigh depth** (review
    001, finding 2; the original commit message claimed otherwise and was
    corrected). **The queue is region-local** — `allocate_region` drains it
    before the next region, and a split copies its bundle's region into both
    halves — and `Block::loop_depth` is the *region's* depth, so every block
    the queue can compare weighs the same. Measured: `hinted_span_weight ==
    count * K_region` on **27,603 of 27,603 bundles** across three inputs, and
    within a region the new rank reorders **nothing** (0 pairs reversed, 0
    distinctions gained or lost over 762 comparable pairs). The win is real
    and measured; the mechanism is "past the first few hints the count is
    noise", and ranking a deep hint above a shallow one **cannot happen from
    this queue**. To actually price a boundary, weigh the block on the far
    side of the `cross_region_affinities` edge instead.
  - The weight rather than the count still buys one thing: it stays correct
    for an embedder whose blocks within one region have different
    frequencies. Cranelift emits none (0 of 19,473 region observations had
    mixed frequency), so on this corpus it is exactly the count.
  - **The sum, not the max.** Variant b (heaviest hinted span) cost the
    `hashset-0004-u0-3` canary **+7.75%** and +2.66% compile insts.
  - **`floor`, not `round`.** Variant c cost countMatches +2.02%.
  - **The field has three bits and that is enough.** Attempt 5 widened it to
    four (taking one from `size`, which had 23 bits for a few thousand spans)
    because the rank saturates on 10.9% of `raytracer-0426`'s hints. It
    changed **nothing** on the 80 heaviest inputs: those were ties the other
    priority fields already broke the same way.
- **`region_preferences` saturates, and fixing it does not help.** It is a
  `RegSet` unioned over every bundle *ever* queued in a region and cleared
  only when the region finishes, so `order_non_preferred_candidates`' "leave
  other bundles' hinted registers free" tier reaches **96% of the class** on
  countMatches and 79% on raytracer-0386 — a no-op under pressure. Counting
  queued bundles instead (attempts 1 and 3) fixes the saturation (79% -> 22%)
  and is still a **substitute for attempt 2, not a complement**: alone -2.42%
  on raytracer-0386, on top of attempt 2 **+1.66%**. Don't revive it without
  re-screening on the tip.
- **`EvictionCost::broken_hints` is a boolean, and that boolean is a cap.**
  Pricing it by hint weight (attempt 4) raised typical compile insts **38%**
  with no codegen gain, and cutting eight tiers to two barely moved it:
  `assign_via_eviction` only takes a *strictly cheaper* victim, so a priced
  hint makes eviction **refuse** victims it used to take, and those bundles
  go on to `split_between_spans`. The boolean was bounding how often eviction
  fails.

Open, ranked (measured at `1ec5260`):

1. **The parent region adopts a child's locations for values live through
   it** (analysis 007/008's own suggested fix). This is where the cost is, and
   010 narrowed it sharply: `dotnet-raytracer-0426-u0-360` honors **242 of
   254 hints** (12 misses, all genuine contention) and *still* spends 60.5M of
   its 66.7M edit cost on register moves — all in single-predecessor,
   single-successor stubs at a loop-depth change, rotating values that are
   **not even arguments of that edge's block call**. Attempts 3 and 4
   exhausted both sides of "who wins the register"; the hint has to bind
   harder than a hint, or the boundary has to be priced into the parent's
   assignment. `reports/code-quality-010/todo/03-tiny-loop-regions.md`.
2. **Price the boundary in the split score** (the seam term earlier sessions
   kept reaching for), now on a corpus where move cost dominates.
3. **Why `tinygo-regex` (+0.85%) and `rust-wasmprinter` (+0.87%) lose under
   attempt 2** while dotnet-raytracer gains 1.31%. Both are reload-dominated
   rather than move-dominated, so a loop-depth hint rank may be the wrong
   trade there. `block_delta.py` on `rust-wasmprinter-0028-u0-21` is the
   cheapest look.
4. **Permutation cycles at a boundary**: a boundary permutation that closes
   into a cycle costs one move more than a chain, because nothing is free to
   start it. Measured, small (0.36% on one input), and probably not fixable
   greedily — whether the ring closes is a global property of several
   independent register choices.
   `reports/code-quality-010/todo/02-permutation-cycles.md`.
5. **A callee-saved cost model** (008 #5): **superseded** — no API
   decision is needed. See the correction at the top.

## Earlier session: `code-quality-009` (2026-10-08, base `cf70ddd`)

`reports/code-quality-009/report.md` in the `regicide-codegen-improvements`
worktree. Against **analysis 006** (`~/regalloc2/reports/codegen-analysis-006/`,
which measured `cf70ddd`). Branch `code-quality-009`: the two `WIP`
commits end at `31bda60`, with this skill update on top. Check `git log`
for whether they landed and under which shas.

| # | idea | verdict | result vs `cf70ddd` |
| --- | --- | --- | --- |
| 1 | color a join's spilled parameters heaviest (parameter, slot) pair first (`4b4de9e`) | **kept** | countMatches -18.2%, regexp.compile -5.0%, tinygo -10.4%; 59 better / 0 worse; slot copies in countMatches 641 → 42 (ion: 49) |
| 2 | spill placement weighs loop depth, not just frequency (`31bda60`) | **kept** | countMatches -14.1% more, regexp.compile -8.8%, sqlite3 -1.3%, VDBE guard -0.6%; 73 better / 1 worse (+6) |
| 3 | an unhinted piece of a split value tries its sibling's register first | dropped at screen | regexp.compile +3.9%; never fires on keccak/blake3 seams (hinted pieces) |

Cumulative: tinygo-regex -17.6%, protobuf -2.2%, sqlite3 -1.6%, hashset
-1.2%; countMatches -29.7%, regexp.compile -13.4%; 96 better / 1 worse;
compile time -0.15%. Two new tests:
`a_param_does_not_take_a_slot_another_param_needs_more`,
`a_spill_for_a_read_after_a_loop_exit_stays_on_the_exit_edge`.

What the code does now, and what to know before changing it:

- **Slot classes and parameter matching** (`spill_slot_allocation.rs`).
  `enter_block` walks a join's parameters once, in parameter order, and
  `param_pairs` tallies each one's votes once into `SlotPair`s, which both
  `match_params` and the unmatched fallback (`best_vote`) read.
  `match_params` matches greedily over the pairs: each free slot a colored
  argument occupies, weighed by `tally_votes`, and the class slot, weighed
  by the larger of that slot's vote and `SlotClasses::weight_in_slot`
  (class affinities whose partner is in that slot or not colored yet; a
  typed range per value into `partner_storage`). Matched slots are then
  **assigned in parameter order**: assigning in pair order reshuffled the
  free list the unmatched parameters fall back to, which cost the VDBE
  guard +50. Weighing the class slot by *all* the parameter's class
  affinities (variant b) cost sqlite3-2507 +3.9%: a parameter held a class
  slot none of its edges reused.
- **A vote beats the class slot on a tie** (review-002 #2, kept by the
  user's decision 2026-10-09). The review asked for the reverse, to keep
  the class's promise. Measured: 12 worse / 6 better, countMatches +260,
  gate fails. The class weight counts uncolored partners optimistically
  (sqlite3-2851: a back-edge argument that later lands elsewhere), while a
  vote is an argument already in the slot. Pinned by
  `a_param_takes_its_arguments_slot_over_a_tied_class_slot`. A rework that
  discounts uncolored partners was offered and not tried.
- **Spill placement weighs `Block::weight`** (`spill_placement.rs`, via
  `Block::runs_more`/`runs_cmp` in `region_tree.rs`, which break weight ties
  by raw frequency since the frequency weight saturates at `COLD`/`HOT`):
  `is_edge_spill_block` and the most-frequent-first order of a value's stack
  blocks use it. Slot classes and `tally_votes` use `Block::weight` too
  (they had a private loop-and-cold weight; review-002 #3 unified them, with
  identical allocation on all 3,179 inputs). An edge store is also taken only
  when the store it replaces (`store_above`) runs more often than the edge;
  without that, 10 small regressions where an edge store sat at the same
  depth as the store above (sqlite3-0121 +100). The push-up step still
  compares frequency only; a probe found it never climbs into a deeper block
  on the 40 heaviest inputs.
- **Not changed, and why:** VDBE head re-stores (analysis 006 #4) are of
  values defined in the loop, so loop depth gives no reason to move them.
- **Slot-class history.** Slot classes landed as `3c6c16c` (code-quality-002
  in this worktree: countMatches -8%). That session's three "loners" variants
  (tags `code-quality-002/loners-*`) failed because they attacked values in
  no class; its backlog #1 ("displaced members cascade") was the parameter
  cascade attempt 1 above fixed. After attempt 1, countMatches has 70
  same-class mismatched pairs (2.8k weight) and 81 cross-class (1k): not
  worth another attempt.

Open, ranked (measured at `31bda60`). **Two of these name `sqlite3` inputs,
which analysis 008's suite dropped**, so their sizes cannot be re-measured;
treat the mechanisms as live and the numbers as historical:

1. **Latch reloads from a loop-wide cut.** countMatches `v3250`: one use per
   iteration (`block1221`, depth 4), but `split_between_spans` cut its
   loop-wide bundle at span 12; the prefix holding the use got `r9`, the
   suffixes spilled whole, and all 7 latches of the depth-4 loop reload it.
   Latch reloads: 629k of countMatches' 4.1M reload cost, 301k of
   `sqlite3-2510`'s 2.2M. This is the split-score seam term again (see
   "Clobbers of hinted registers" below for what has failed).
2. **machine.add arm stubs** (006 #2): 6.6k of 11.5k est. cycles are edits in
   single-successor stubs; 8 early exits store loop-carried `v67..v69`,
   `v119`, `v120` for the exits' join. The stores are already on edges at the
   loop's own depth, so attempt 2's rule has nothing to move.
3. **Fixed-register moves** (call arguments) are the largest deep-loop move
   class in 7 of the 14 heaviest functions (78% in `sqlite3-2492-u0-1910`,
   94% in `sqlite3-1504-u0-1159`). Cost 1 each.
4. **Callee-saved cost model** (006 #3): **superseded** — no API change is
   needed. See the correction at the top.

## Analysis 009 (2026-10-13, regicide `4fa422a`)

`~/regalloc2/reports/codegen-analysis-009/`. The **current** analysis, and
the one `code-quality-011` worked against. Same `default.suite` as 008, so
their corpora are comparable; it measured the tip that 010 and
`compile-speedups-005` had landed.

Top line on wall time: geomean **-0.31%** over 26 benchmarks, **12
significantly faster against 2 slower** — regicide wins six times as many
benchmarks as it loses, and 12 of 26 are outright parity.

| benchmark | cycles | note |
| --- | --- | --- |
| `shootout-xchacha20` | **+7.61%** | the largest regression, and **not regicide's**: `chacha20_rounds` is byte-identical across the 11 commits |
| `tinygo-regex` | **+2.67%** | down from +10.28%, and **attributable to regicide** (124 of 265 functions changed) |
| `shootout-keccak` | **-5.09%** | the largest win, on **+8.42% instructions** |
| `ocaml-raytrace` | -4.50% | |
| `rust-protobuf` | -4.32% | |
| `rust-wasmprinter` | -3.34% | predicted **+0.87%** by the previous step-3 session — an inverted sign |

Its **five "things to fix"**, and status after code-quality-011:

1. **The parent region does not adopt a child loop's locations.** **Partly
   addressed**: the hint-reachable part is fixed (the clean target -2.44%,
   its siblings -5.80% and -5.31%, exit-stub cost 39.4M -> 7.0M). The
   remainder is out of scope; see 011's open #2.
2. **Nothing else in the suite is a significant regression** — it bounds the
   work rather than naming one. "Further codegen work on this suite needs a
   new benchmark set to find anything, or has to accept that it is
   optimizing static metrics with no wall-time signal."
3. **Judge `starlingmonkey-markdown` statically** (+10.04% insts against
   +1.82% cycles, `NOISY` even at 300 samples). **Followed**; it is -0.46%
   at 011's tip and no wall-time claim rests on it.
4. **`hashset` is unmeasurable on this host — stop citing it.** Its CV
   *rises* as n doubles, and its sign is not reproducible across five
   analyses. With `hoot-earley-boyer` now explained as host-bound, "the cost
   model is missing a term" is **open and unevidenced, not established**.
5. **The static cost model is concentrated on two benchmarks**:
   `dotnet-raytracer` 82.6% and `starlingmonkey-markdown` 16.1% =
   **98.7%**. Gate on per-module numbers plus the wall-time guards, never
   the suite total alone. Note `shootout-keccak` is **0.0005%** of static
   cost and the run's largest wall-time win.

Its "things we do well" (all byte-identical at 011's tip): keccak's remat
and 336-byte frame — and **ion emits 23 store-then-reload pairs within 4
instructions where regicide emits 0**; whole-function coalescing
(`encode_varint` 53 -> 18 moves); loop-carried values in registers
(`rust-wasmprinter` stack accesses **-45.4%**, `dart-deltablue` -38.7%);
managed runtimes as regicide's strongest family; and slot-to-slot copies
now **better than ion** (579 against 608).

**Compile time vs ion is +173% geomean, 29 of 29 slower** — measurement
only, feeding no ranking.

## Analysis 008 (2026-10-09, regicide `7e8f866`; superseded by 009 above)

`~/regalloc2/reports/codegen-analysis-008/`. The **current** analysis, and the
one that replaced the benchmark suite (see the note at the top). Regicide was
unchanged from analysis 007, so 008 measures the same allocator against a
different, larger benchmark set; the seven carried-over benchmarks reproduce
to within 0.6 pp, which cross-checks both runs.

Top line on wall time: geomean **-0.64%** over 26 benchmarks, 13
significantly faster, 6 slower. **Regicide is net faster than ion**, and the
managed-runtime family carries the win now that `sqlite3` is gone:
`kotlin-richards` -8.85%, `ocaml-raytrace` -5.11%, `dart-deltablue` -2.52%,
`java-navier-stokes` -2.21%, `dotnet-raytracer` -1.60%.

Corpus: a single `corpus/` of **33,038 inputs** (13,926 distinct), all 29
modules. Suite estimated cycles at `7e8f866`: **7,638,047,244**;
`coalesce-out-of-fuel` 0 everywhere.

| benchmark | cycles | function / input |
| --- | ---: | --- |
| `tinygo-regex` | **+10.28%** | `countMatches`, `tinygo-regex-0107-u0-99` |
| `starlingmonkey-markdown` | ~+3 to +7% (NOISY) | largest module, 18,037 inputs |
| `shootout-xchacha20` | **+6.28%** | `chacha20_rounds`; identical code, register permutation only |
| `hashset` | ~+3% (NOISY) | instructions disagree in sign |
| `hoot-earley-boyer` | +1.46% | better on every static count, measurably slower |
| `libsodium-siphashx24` | +0.64% | callee-saved pair (fix #5) |

Its five "things to look into", and status after code-quality-010:

1. **The cost model is missing a term** — `hoot-earley-boyer` retires 2.4%
   fewer instructions, touches 3.8% less stack *and* makes 20.8% fewer moves,
   and is 1.46% slower; `hashset` is the mirror. The two disagree in sign on
   moves, so it is not "moves are underpriced". **This is the metric step 3
   optimizes against**, which makes it the broadest item. Needs a profile
   under both allocators — the analysis skill's job, not step 3's.
   **Untouched**; `hoot` moved ±0.00% under every 010 attempt.
2. **Register choice alone can cost 6%** (`shootout-xchacha20`): 99
   instructions, identical opcodes in identical order, 0 stack and 0 moves
   under both allocators, differing only in which registers they name;
   survives 64-byte alignment. A calibration point for how much wall time can
   move with allocation quality held constant. **Untouched, and no static
   metric can see it.**
3. **Loop-exit stubs** (`tinygo-regex`): the child region wins registers for
   loop-carried values and the parent picks the join's locations
   independently, so the exit edge pays the difference. Break-even is 3.1
   iterations against `block_weight`'s assumed 10. **Partly addressed** by
   010's attempt 2 (-2.97% on the corpus's heaviest function, its depth-7
   boundaries 17 moves -> 10 and 11); the general fix is open as 010's #1.
4. **`starlingmonkey-markdown` is win-shaped but measures as a loss.**
   **Untouched by design**: the analysis says it is NOISY (CV 12.2/18.7) and
   that nothing should be built on it without more samples.
5. **A callee-saved cost model** (`siphashx24`): **the API half of this is
   superseded** — see the correction at the top. `Machine`'s class order
   already names the convention, and the `index >= 16` rule was reading it
   correctly, just hard-coded to one class shape. The counterweight still
   stands and still grew: preserve item #1 is built on callee-saved
   registers held across calls. **Price the pair once per function; do not
   avoid callee-saved registers.**

Its guards (all byte-identical at 010's tip): `dart-deltablue` <= 1,991
`[sp]`, `kotlin-richards` <= 3,006, `ocaml-raytrace` <= 2,199; keccak's
store-then-reload count at 0 and its 336-byte frame; `coalesce-out-of-fuel`
0 corpus-wide; protobuf <= 1,599 `[sp]` and 5,774 moves; per-iteration stack
accesses in countMatches' inner loops; tinygo slot-to-slot copies <= 397.

**Compile time vs ion is +249% geomean, 29 of 29 slower** — measurement
only, not analyzed, and it feeds no ranking.

## Analysis 006 (2026-10-08, regicide `cf70ddd`; superseded by 008 above)

`~/regalloc2/reports/codegen-analysis-006/`. On cycles only **tinygo-regex
(+21.4%)** and **siphashx24 (+1.25%)** are regressions; sqlite3 (-4%),
keccak, hashset and kotlin-richards are cycles *wins* despite more
instructions (regicide trades memory for register moves). Corpora:
`corpus-{blake3,hashset,keccak,kotlin,protobuf,siphashx24,sqlite3,tinygo-regex}/`
(3,179 distinct inputs). Its `corpus-*.stderr` files sit beside them: glob
with `corpus-*/`.

| benchmark | function | input |
| --- | --- | --- |
| tinygo-regex | `countMatches` | `tinygo-regex-0107-u0-99` |
| tinygo-regex | `regexp.compile` (slot-copy signature, cold at runtime) | `tinygo-regex-0252-u0-239` |
| tinygo-regex | `(*machine).add` | `tinygo-regex-0241-u0-229` |
| tinygo-regex | `MatchRunePos` (preserve: whole-function coalescing) | `tinygo-regex-0235-u0-223` |
| sqlite3 | VDBE (preserve: pointers in callee-saved) | `sqlite3-0226-u0-181` |
| kotlin-richards | `function[71]` (preserve: inner loops in registers) | `kotlin-richards-0086-u0-64` |
| hashset | `benchmark()`, `rehash` | `hashset-0004-u0-3`, `hashset-0009-u0-8` |
| rust-protobuf | `encode_varint` | `rust-protobuf-0039-u0-31` |
| keccak | `keccak_core` (preserve: remat, small frame) | `shootout-keccak-0005-u0-4` |
| siphashx24 | core (in-loop parity; fix #3) | `libsodium-siphashx24-0044-u0-34` |

Its five "things to fix", and status after code-quality-009: #1 slot-class
promises **addressed** (attempt 1); #2 loop-exit stubs **partly** (attempt 2
moved the stores; the stubs' reloads and machine.add's permutations remain);
#3 callee-saved **open** (API); #4 VDBE head re-stores **open** (small in
the estimate); #5 keccak/blake3 seam moves **open** (no cycles cost).

## `code-quality-001` (2026-10-06, base `bf6be7d`)

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
3. **Callee-saved as a `Machine` property** (fix #3). **Superseded** — see
   the correction at the top. The order *is* the property, and is more
   expressive than `non_preferred_regs_by_class`; 003's `index >= 16` probe
   was reading the real convention. No API change, no need to ask.
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

## Analysis 003 (2026-10-06, regicide `e9b676b`; superseded by 006 above)

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
   the save/restore, passed `--check`, and left corpus totals neutral. The
   probe hard-coded the tail as class index >= 16 (or 24), and that is why
   it was shelved. **2026-10-14: that hard-coding was reading the real
   convention** — class member order is caller-saved-first by construction
   (`machine.rs:783`), so the probe generalizes by keying off *position in
   the class order* instead of a literal index. No API change is needed; see
   the correction at the top. 001's in-scope proxy (rank registers past the
   furthest one in use last) regressed keccak and blake3 and was dropped —
   note it is a different and weaker idea than keying off class order. The
   estimate cannot see the prologue save/restore, so judge any fix on the
   register set used, not the estimate alone. **Status: open and in scope —
   this is the most concrete form of the callee-saved item, and it already
   has a probed fix.**
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

## Traps from code-quality-011

- **Both halves of a critique can be right and both fixes worthless.**
  `region_preferences` is saturated, stale and ~60% too wide. Attempt 4
  fixed its lifetime, attempt 6 its width, and **both left both targets at
  exactly +0.00%** — because the saturation was a symptom of hints pointing
  at the wrong registers, which attempt 1 had already fixed. **Before
  fixing a data structure that measures badly, check that anything still
  depends on the measurement.**
- **Plain counts can improve on every axis while the estimate rises 4.6%.**
  The skill's standing example of counts-vs-estimate disagreement runs the
  other way (a count *rise* that is the intended trade). This is the mirror,
  and the more dangerous direction: a session screening on counts would
  have shipped attempt 6's 432 fewer spills and 407 fewer reloads as a win.
- **A "how many decisions change" count does not rescue a near-constant
  ranking key.** Attempt 3's variance probe said the far-side block weight
  varies for only 21 of 176 conflicts; a second probe said 61 of 176
  decisions would change, and that second number is what talked me into
  building it. The 61 changed to whatever the cheap rule already picked.
  **Stop at the variance probe.**
- **Read the instructions around an edit before calling it redundant.** 148
  repeated `(from, to)` moves inside single blocks, worth 19.5M on one
  input, looked like a clean redundancy in the edit list. The calls between
  them clobber `r0-r15`; every repeat is necessary. Every script here
  summarizes edits by design, which is where this trap lives.
- **Revive a dropped idea by cherry-picking its tag.** `git cherry-pick
  --no-commit code-quality-NNN/<slug>` still applies cleanly across
  sessions, and turned a half-session's reimplementation into two minutes
  and a decisive answer.

## Traps from code-quality-010

- **A set that only grows saturates, and a heuristic reading it goes dead.**
  `region_preferences` unioned every bundle ever queued in a region and was
  cleared only per region, so the "leave other bundles' hinted registers
  free" tier saw 96% of the class marked preferred on countMatches. One
  `trace!` counting `preferred / class` at each call found it in minutes.
  **Worth checking any "avoid what others want" rule the same way.**
  **But see the qualification below: code-quality-011 fixed both the
  staleness and the width, and neither was worth anything.**
- **Two changes aimed at one cost can each help and still not compose.**
  Attempt 1 took the heaviest input -2.42% alone; the identical patch on top
  of attempt 2 took it **+1.66%**. They were substitutes, not complements.
  **Always re-screen a revived idea on the current tip** rather than assuming
  it adds to what landed since.
- **A field that only ever holds 0 or 1 may be a cap, not an
  under-specified cost.** Pricing `EvictionCost::broken_hints` by hint weight
  cost **+38% compile time** with no codegen gain, and cutting eight tiers to
  two barely moved it: `assign_via_eviction` takes only a strictly cheaper
  victim, so a priced hint makes it *refuse* victims and pushes the work into
  `split_between_spans`. This is the "lifting a cap costs compile time" trap
  in a shape the pitfall list did not name.
- **"The field saturates" is not "the saturation decides anything."**
  `hint_rank`'s 3-bit ceiling was hit on 10.9% of one target's hints, so 010
  widened it. It changed **nothing** on the 80 heaviest inputs: those were
  ties the other priority fields already broke identically. Screen a
  widening on the heaviest inputs before writing it up as a candidate.
- **A 97% hint hit rate can coexist with a huge move cost.**
  `dotnet-raytracer-0426-u0-360` honors 242 of 254 hints and still spends
  60.5M of 66.7M edit cost on register moves. The skill already says to
  measure hint *width*, not just hit rate; this adds that **a high hit rate
  does not mean hinting is the lever at all**. Classify the heavy blocks by
  CFG position (`boundary_moves.py`) before attributing cost to hints.
- **A release rebuild can differ byte-for-byte after a test-only edit.**
  Twice in 010 an amend that only touched tests, or deleted a now-unused
  function, produced a different binary that allocated identically. **Verify
  TSV reuse by comparing estimated cycles on the targets, not by `cmp` on the
  binary.**
- **`counts.py` and a concurrent `cargo build` contend on the build lock.**
  Two full-corpus runs stalled for minutes behind "Blocking waiting for file
  lock on build directory", which looks exactly like the stuck-replay
  pitfall. Check for a running cargo before running `ps` on the `run-*`
  children.

## Tooling facts

- **`counts.py -j 12` over analysis 009's corpus takes about 6 minutes**
  (13,928 distinct of 33,038 captures), not the ~25 `SKILL.md` budgets for
  008's. All 13,928 come back `ok`; the slowest are the two `tinygo-regex`
  inputs at ~42 s each.
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
  `a_value_unused_in_a_loop_is_not_reloaded_inside_it`. At `cf70ddd`: 421 +
  8; at `31bda60` (code-quality-009, after review-002): 425 + 8. At
  `7e8f866`: **428 + 8**, and at `1ec5260` (code-quality-010) 429 + 8. At
  `4fa422a` (analysis 009's revision): **431 + 8**, ~100 s; at `1902b8a`
  (code-quality-011) **432 + 8**, the extra being
  `a_settled_hint_displaces_speculative_ones`. No fixture needed re-blessing
  for that change.
- **Tests that pinned an allocation shape changed with 001 #2.**
  `a_move_into_a_register_nothing_reads_goes` and the `dead-edits` visualizer
  fixture now use `TestInput::with_a_register_move_overwritten_in_a_later_block`
  (found by a mutatis shrink). `with_a_looping_value_read_only_after_the_loop`
  no longer yields a dead move. Neither the test corpus nor 100,000 mutated
  inputs yielded a dead register move inside a loop under 001 #2.
- **`$S/block_delta.py BASE.txt CAND.txt`** ranks a function's
  estimated-cycles delta by block and loop depth, from the two `run`
  printouts. It replaces the `block_costs.py` + `block-costs.patch` pair the
  skill used to describe, which **never existed on `main`** — those needed a
  patched scratch build; this needs none, because block ids are stable
  between two allocations of one input. In code-quality-003 the older tool
  explained every regression in minutes; in 010 this one did the same.
- **The scripts in `scripts/` were out of sync with the skill until
  2026-10-09.** `SKILL.md` referenced `loops.py`, `edit_costs.py`,
  `scratch.sh`, `block_costs.py` and `block-costs.patch`; only `counts.py`
  and `diff_counts.py` were actually committed (`git log --diff-filter=A`
  confirms). code-quality-009 reported adding them, but that worktree's
  copies never landed. 010 rewrote and committed working equivalents. **If a
  script the skill names is missing, check `git log` rather than assuming the
  worktree is broken** — and write the replacement into `scripts/`, not just
  the report.
- **`$S/scratch.sh DIR [REV]`** makes a buildable scratch copy for probes and
  patched builds. A `git archive` of `src examples` alone fails: the crate
  `include_str!`s `README.md` and `visualizer/` files, and the workspace
  needs `fuzz/Cargo.toml`. `cp` is aliased verbose on this host, and the
  fuzz corpus is huge: never copy `fuzz/` whole.
- **`$S/edit_costs.py PRINTOUT [--latches]`** weighs one input's edits by
  kind and loop depth, and sums latch reloads. At `31bda60`, countMatches:
  depth-4 reloads 3.2M of 11.0M est. cycles, latch reloads 629k.
- **`$S/boundary_moves.py` and `$S/exit_stubs.py`** split an input's edit
  cost by CFG position: loop-entry, loop-exit and interior blocks, and the
  exit stubs ranked. In code-quality-010 this reframed the session —
  **53% of all move cost over the four heaviest inputs sat on a loop
  boundary**, and 59-66% of *all* edit cost on the two `dotnet-raytracer`
  inputs.
- **`$S/hint_votes.py LOG`** (added by code-quality-011) tallies, per
  bundle, how many region borders asked for each register against what the
  bundle was assigned. It found that session's kept change: 25 of 254
  hinted bundles on `raytracer-0426` took a register fewer borders asked
  for. It reads `BundleHint`, logged from `regicide::live_ranges`, so it
  needs **`RUST_LOG=regicide=trace`**, not the `region_allocation` target
  the other event scripts use. Only single-register hints vote — a
  whole-class hint names a class rather than a place, and counting it
  drowns the ones that name a register.
- **`$S/hint_misses.py` also classifies the input, not just the hint.**
  100% "holder took it as its own hint" means a pure-boundary input
  (`raytracer-0426`); a three-way split means real register pressure
  (`-0385`: 111 contention, 83 a different hint, 24 unhinted). That is the
  fastest way to tell which of the two problems you are looking at.
- **`$S/selftest.py`** checks the printout and event scripts against the
  three bugs review-001 found in them: a self-loop swallowing the dominator
  chain, an unreachable `entry` bucket, and an event reader blind to
  eviction. Each case was verified to fail when its bug is reintroduced, and
  `test_boundary_buckets_can_fire` drives `boundary_moves.classify` on a
  synthetic printout rather than restating its rule — an earlier draft
  restated it and passed with the bug back in.
- **The printout scripts share `loops.py`**, and `python3 -I` drops a
  script's own directory from `sys.path`, so a bare `import loops` fails
  under the `-I` the environment asks for when reading untrusted corpora.
  They each insert their own directory explicitly; keep that shim if you add
  another. All eight were verified with and without `-I`, from an unrelated
  cwd, on 2026-10-09.
- **`$S/hint_misses.py LOG`** classifies, from a
  `RUST_LOG=regicide::region_allocation=trace` log, why each hinted bundle
  missed its hint: the holder wanted it too (real contention), wanted a
  *different* register (a tie-break failure), or was unhinted. Needed to tell
  "hinting is the lever" from "it is not".
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

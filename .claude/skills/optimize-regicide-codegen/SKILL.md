---
name: optimize-regicide-codegen
description: >
  Improve the quality of the code `regicide` allocates: fewer register-register
  moves, spills, reloads and spill slots, above all in hot (loop-nested,
  non-cold) blocks of the functions a benchmark spends its time in. Use when
  asked to improve regicide's codegen or allocation quality, act on a
  `codegen-analysis-NNN` report from the `analyze-regicide-codegen` skill, fix
  one of its findings ("fix #2 from analysis 003"), or reduce regicide's
  moves, spills, reloads or frame sizes -- driving the work empirically by
  replaying that report's captured corpora through `examples/run.rs` and
  comparing estimated cycles. Produces a series of `WIP` commits, one per kept
  improvement, and a `reports/code-quality-NNN/` directory.
---

# Optimize regicide's code quality

Your job is to make the code regicide allocates **cheaper to run**, measured
statically over captured allocator inputs, and to leave behind (1) a series of
`WIP` commits that each improve it and (2) a report of everything you tried,
including what did not work.

This is the sibling of `optimize-regicide-compile-time`, inverted: there the
allocation must not change, here changing it **is** the deliverable, and
compile time is a budget you must not blow.

It is step 3 of a loop whose steps 1 and 2 are the `analyze-regicide-codegen`
skill in `~/regalloc2`:

1. Run sightglass, regicide vs regalloc2's backtracking (ion) allocator.
2. Analyze why regicide is slower or faster on each benchmark. → a
   `~/regalloc2/reports/codegen-analysis-NNN/` report.
3. **Implement improvements based on that analysis.** ← you do this
4. Repeat: the user re-runs the analysis on your tip.

**Before you start, read `references/known-findings.md`**: what the latest
analysis found, which corpus inputs are its hot functions, and the traps
earlier sessions fell into. Re-verify anything load-bearing; regicide changes
quickly, and the user works on it in parallel branches.

## The metric: estimated cycles

`examples/run.rs` prints, per input and in its totals:

```
  moves 400  spills 873  reloads 990  remats 190  critical-edges 0  slots 42
  of which cold: moves 0  spills 0  reloads 0  remats 0
  estimated-cycles 21559.0  reg-operands 11654.0  stack-operands 0.0  moves 400.0  remats 190.0  spills 873.0  reloads 990.0
```

**Estimated cycles is the number that decides.** Each operand and edit costs:

| item | cost |
| --- | --- |
| register operand, register-register move, remat | 1 |
| stack operand, spill, reload | 5 |

times its block's weight, which is **10x per enclosing loop** (from regicide's
own region tree, via the `#[doc(hidden)]` `Output::loop_depth`) times a
**frequency weight**: 0.05x for a cold block, 1x normal, 10x hot, log-log
interpolated in between (`EstimatedCycles::block_weight`). The components after
the total are those weighted counts, so a change in the total can be traced to
what moved.

Things to know about it:

- **It is static.** Loop depth and Cranelift's frequency hints stand in for
  execution counts. Today Cranelift only reports `COLD` or `NORMAL`, never
  `HOT`, so the frequency weight is 0.05 or 1 in practice.
- **It ignores the instructions themselves**: latency, ILP, the cost of a
  call. It is only for **ranking two allocations of the same inputs**. Never
  compare it across different inputs or corpora.
- **It is not the analysis skill's "virtual cycles"**, which uses 10x for
  the stack and no weights. Do not mix the two numbers.
- **Plain counts are secondary.** A plain-count rise with lower estimated
  cycles is often the intended trade (moves pushed into cold blocks, a reload
  hoisted out of a loop). Say so in the write-up; do not treat it as a
  regression.
- **Spill slots** are not in the estimate. Watch `slots` separately: all else
  equal, smaller frames are better (a thing to preserve, see known-findings).
- **Cold edits barely register.** At 0.05x, cutting cold moves by half in
  every corpus (code-quality-003) moved no corpus total by more than 0.5%.
  When the change is about slow paths, report `diff_counts.py`'s `cold moves Δ`
  column next to the estimate.
- **It charges every block at its own weight, as if each ran that often.** So
  merging edits that sibling paths each make (one copy per predecessor of a
  join, sunk into the join; or the mirror, hoisted out of a branch's arms)
  looks like a win although each path still runs exactly one copy. Before
  trusting a saving from moving edits between siblings, ask whether the
  dynamic count on any one path changes. If not, it saves code size, not
  cycles, and is out of scope (code-quality-009's
  `unsuccessful/sink-common-pred-moves.md`).

## Invariants

Breaking any of these invalidates the improvement, however good its numbers.

- **The checker passes on every allocation.** `counts.py` runs `--check` on
  every input by default; a `checker-failed` row fails the gate.
- **Tests pass.** `cargo test --all-features` green, checking cargo's own exit
  code (see "Testing").
- **No new `unsafe`.**
- **Measure, don't intuit.** Every claim traces to a count from `counts.py` /
  `diff_counts.py` or a quoted allocation diff. "This should reduce spills"
  is not a finding.
- **No pessimization of the guard list.** The analysis's "things we do well
  and must preserve" become guard functions in `targets.tsv`; their estimated
  cycles must not rise.
- **Read the allocation diff of every target function's hot blocks**, every
  hunk. It is your primary evidence, the way a bless diff is for Cranelift. It
  must show the improvement you intended and nothing else. An unexplained hunk
  is a bug until explained; a hot-block hunk that got worse is a pessimization
  you are about to ship.
- **Stay in scope** (below).
- **One idea per `WIP` commit**, and **failed attempts are also committed**,
  tagged, and dropped (see "Git").
- **Write the report as you go.** After every attempt, before starting the
  next. A reboot must cost at most the attempt in flight.
- Match the surrounding code's style; load the `writing-code-comments` skill
  before writing comments.

## Scope: what you may change

**In scope:** anything inside the allocator that decides where values live:
split-point selection and scoring, eviction and priorities, the cost model,
hint generation and honoring, coalescing, spill placement, spill-slot
allocation and reuse, remat decisions, move generation and the move
elimination passes, and small analyses computed inside an existing pass. Plus
the unit tests that cover them.

**Off limits unless the user explicitly asks:**

- The public input, `Machine` or `Output` API, or the serialized input format.
  Changing them breaks every captured corpus and regalloc2's integration.
- New passes in the pipeline, or rearchitecting an existing one (the region
  tree, liveness, the region allocation loop).
- The checker.
- regalloc2, Wasmtime or Cranelift.

If the fix genuinely needs one of those, **stop and say so**, with what you
found and what it would take, rather than starting it.

## Inputs

- **The analysis report.** If the user names one, use that. Otherwise the
  **highest-numbered** `~/regalloc2/reports/codegen-analysis-NNN/`. Read its
  `report.md`, then each `regressions/` and `improvements/` file a finding
  cites.
- **Corpora.** Every non-empty `corpus*` subdirectory of that report (check
  `find <dir> -type f | wc -l`; `corpus/` itself has been seen empty), **plus
  any corpora from earlier reports that its findings were analyzed on**. 003,
  for example, analyzed tinygo-regex and sqlite3 on 002's corpora. Never
  write into those directories; they belong to another workflow.
- **Which findings** (optional). Without a choice, work down the report's
  "Top N things to fix" in its order, which is already cost × breadth.
- **Time budget** (optional). Without one, keep going until the backlog has
  nothing you have a credible idea for, then write up.

## Layout of the report directory

```bash
cd <repo root>                      # this worktree; never `cd` elsewhere
ls reports/                         # find the highest code-quality-NNN
R=reports/code-quality-001          # next unused number; set in every shell
A=~/regalloc2/reports/codegen-analysis-003   # the input analysis
S=.claude/skills/optimize-regicide-codegen/scripts
mkdir -p $R/{successful,unsuccessful,todo,counts,diffs,bins,logs,misc,patches}
```

`reports/` is gitignored (by `~/.gitignore`), so nothing in it is committed.

| Path | Holds |
| --- | --- |
| `report.md` | Status, inputs, baseline, every attempt, cumulative result, findings coverage. Created first, updated after every step. Template in `references/report-templates.md`. |
| `targets.tsv` | Target and guard functions for `diff_counts.py` (see "From analysis to backlog"). |
| `todo/NN-<slug>.md` | One candidate per file, before it is tried. |
| `successful/<slug>.md` | One per kept improvement. Moved from `todo/`. |
| `unsuccessful/<slug>.md` | One per dropped attempt, with its tag. Moved from `todo/`. |
| `counts/<sha>.tsv` | `counts.py` output per measured commit. |
| `diffs/` | `diff_counts.py` output, and target-function allocation diffs. |
| `bins/` | `run-<sha>` for each commit measured. `target/` is overwritten by the next build. |
| `logs/` | Event logs and tallies from replaying target inputs. |
| `misc/` | Environment, test and fuzz logs, tool gotchas, and **suggested additions to this skill** (`misc/skill-learnings.md`). |
| `patches/` | Only if `git commit` is refused (see "Git"): `NN-<slug>.patch` per attempt, in place of commits and tags. |

Put the date and time (`date '+%Y-%m-%d %H:%M'`) at the top of every file you
write, and the commit sha every measurement was taken at.

## 0. Setup

1. Create `$R` and a skeleton `report.md` (status: "setting up").
2. **Record the environment** into `$R/misc/environment.md`: `date`,
   `git rev-parse HEAD`, `git status --short`, `rustc -V`, the analysis
   report path and the regicide sha *it* measured (in its header), and the
   corpora list with input counts.
3. **Branch.** Work on a fresh branch off the current `HEAD`, e.g.
   `git switch -c code-quality-NNN`. Note the base sha in `report.md`.
4. **Check what is in flight.** `git branch -a` and
   `git log --all --oneline --since=<analysis date> -- <files a finding
   blames>`. The user works on regicide in other worktrees (e.g.
   `splitting-and-blocks`, `eviction-priced-by-satisfied-hints`). Read-only:
   note in `report.md` how each finding relates to in-flight work, and say so
   before duplicating it. Also check whether the analysis's finding is already
   fixed between the sha it measured and your base.
5. **Baseline tests** on the untouched tree (see "Testing"). Then a red test
   later is yours. For pre-existing failures, check the user's memory notes.
6. **Baseline counts.** Build (see "Build"), then:

   ```bash
   python3 $S/counts.py -b $R/bins/run-$sha -o $R/counts/$sha.tsv \
       $A/corpus-*/ <cited earlier corpora> 2> $R/misc/counts-$sha.log
   ```

   Keep the trailing `/`: analysis 006 has `corpus-*.stderr` files beside its
   corpus directories, and `$A/corpus-*` feeds them in as `failed` inputs.

   Run it in the background and do "From analysis to backlog" meanwhile.
   **Another worktree may already have this TSV** (`git worktree list`, then
   `reports/code-quality-*/counts/<sha>.tsv`): if its `bins/run-<sha>` is
   byte-identical to yours (`cmp`), copy the TSV and say so in
   `environment.md`. Every row must be `ok` or `skipped`; a `failed` row on
   the untouched tree usually means the corpus predates an input-format
   change, and that corpus cannot be used. A `timeout` (default 900 s) marks an input to keep out of
   every comparison; note it.

## 1. Build

```bash
sha=$(git rev-parse --short HEAD)
cargo build --release --example run
cp target/release/examples/run $R/bins/run-$sha
```

The `run` example links regicide with its dev-dependency features (`checker`,
`trace-log`, `visualizer`, `timing`, ...). None of them changes an allocation
decision, so its counts are production's. Its instruction counts include event
construction that production does not pay (~0.3%), which is fine for
comparing two builds.

## 2. From analysis to backlog

1. **Targets.** For each hot function the analysis names, find its corpus
   input. The per-benchmark reports list them (`u0-N.postcard`). Corpus
   `u0-N` is **not** disassembly `function[N]`: imports shift the index, and
   each report gives its offset. Write `$R/targets.tsv`:

   ```
   # role	regex (searched in the input's name)	label
   target	tinygo-regex-0107-u0-99$	tinygo countMatches, fix #1
   guard	hashset-0009-u0-8$	hashset rehash, preserve #2
   ```

   Anchor each regex with `$`. Without it, `u0-9` also matches `u0-99`. The
   name `diff_counts.py` searches has no `.postcard`, so `u0-99\.` matches
   nothing. `diff_counts.py` fails the gate if a regex matches nothing, so a
   typo cannot silently gate nothing.
2. **Guards.** Every "thing we do well" with a corpus input becomes a
   `guard` row.
3. **Candidates.** One `todo/NN-<slug>.md` per idea: the finding it
   addresses, the mechanism (from the analysis, then re-derived; see below),
   the target inputs, the event-count signature you expect to move, an
   **estimated saving in estimated cycles** on the targets, and its breadth
   (how many corpora show the signature). Rank by estimated saving × breadth.
   A finding the analysis calls "cheap per occurrence" may be worth little;
   one in the innermost loop of a hot function is worth a lot.
4. **Cheap probes first.** An analysis often records a one-line probe it
   already ran (e.g. 003's callee-saved ordering). Those make good first
   attempts: the mechanism is known, and they shake out the workflow.

## 3. Reproduce before changing

Do not change regicide until you can see the problem in the target input.
This is the counterpart of Cranelift's "minimal `.clif` reproducer first": a
replay of one function is a fast loop; a whole corpus is not.

```bash
# The allocation, block by block, with every operand's location and edit.
$R/bins/run-$sha $A/corpus-X/<target>.postcard > $R/logs/<target>-$sha.txt

# The decisions behind it, tallied by kind.
RUST_LOG=regicide::region_allocation=trace,regicide::coalescing=trace \
    $R/bins/run-$sha -q $A/corpus-X/<target>.postcard 2>&1 \
    | grep -oE "event: [A-Za-z]+" | sort | uniq -c | sort -rn \
    > $R/logs/<target>-$sha-events.txt

# For splits and live ranges, the HTML visualization.
cargo run --release --example visualize -- \
    --input $A/corpus-X/<target>.postcard $R/logs/<target>-$sha.html
```

- **Weighted, not counted.** A printout's plain edit counts mislead: one
  depth-4 reload outweighs 10,000 at depth 0. `$S/edit_costs.py` (with a
  `BLOCK_COSTS=1` dump, see step 6 of "The loop") weighs them.
- **Find the hot block in the printout** with `$S/loops.py`. It finds the
  back edges and natural loops in a `run` printout and lists each loop's
  blocks with their edit tallies, innermost first. Hot means inside the
  innermost loop and not cold. The analysis says which loop.

  ```bash
  python3 $S/loops.py $R/logs/<target>-$sha.txt | less
  ```

- **Find a small reproducer.** A hot target can have hundreds of thousands
  of queue pops, too many to read a decision trail. Scan the corpus for
  small inputs with the same signature, then read one of those in full
  (`RUST_LOG=trace`). For back-edge reload seams:

  ```bash
  # Inputs under 5e7 compile insts that spill at all, smallest first.
  awk -F'\t' 'NR==1 {for (i=1; i<=NF; i++) c[$i]=i; next}
      $c["status"]=="ok" && $c["insts"]<5e7 && $c["spills"]>0 \
      {print $c["insts"]"\t"$c["path"]}' \
      $R/counts/$sha.tsv | sort -n | cut -f2 \
      | while read f; do $R/bins/run-$sha "$f"; done \
      | python3 $S/loops.py --latch-reloads 3 /dev/stdin
  ```

  In 001, `sqlite3-1347-u0-1026` (a 3-block loop, 4 latch reloads, 147 queue
  pops) showed the whole split-and-evict cascade in one screen. The target
  it stood for, `countMatches`, had 242,695 queue pops.
- **Check whether any operand moved before blaming a decision.** In a big
  function, a change can move ±2% of estimated cycles without changing one
  `use`/`def` allocation: slot numbering shifts, so redundant-move elimination
  removes a different set of moves. Compare the `use`/`def` lines block by
  block (code-quality-003's `misc/operand_changes.py`). If none moved, rerun
  both sides with `-r none`: if the ranking holds there, the cost is real;
  either way, it is not a hot-loop decision your change made.
- **Re-derive the mechanism from the event counts.** The analysis's
  mechanism is a hypothesis about the code as it was. 001's explanation of
  the switch regression was wrong, and 002 found the real one from event
  counts.
- The method for reading an allocation (the "why" ladder, event-to-question
  table, signature ratios, log targets) lives in the analysis skill. Read it
  there rather than re-deriving it:
  `~/regalloc2/.claude/skills/analyze-regicide-codegen/references/analyzing-allocation.md`
  and `.../references/tools.md`.
- Where the heuristic lives in a module with unit tests, and the situation
  can be built small (see `src/test.rs`), add a test that pins the behavior
  you want. It is the cheapest regression guard you can leave behind. **Check
  that it fails without your change.** Disable the change for one run of the
  test (e.g. `false && ...`). 001's first test input passed at base, because
  the allocator never hit the case it was built for.
- **Measure the signature with a scratch probe** when no event says it
  directly: `$S/scratch.sh /tmp/probe [REV]` makes a buildable copy (a bare
  `git archive` of `src` and `examples` does not build; see the script), add
  `trace!("PROBE ...")` lines where the decision is made, build there, and
  tally with `awk` or a short Python script. Never probe in the worktree.
  Save the probe as a patch and any tally scripts in `$R/misc/` so the
  numbers in `todo/` can be reproduced.
  - Save the raw stderr and pull the probe lines out with `grep -a PROBE`.
    Log lines carry a timestamp prefix, so `^PROBE` matches nothing. In
    code-quality-009 a macOS `sed` over the raw log silently lost 3,300 of
    3,533 probe lines on countMatches, where `grep -a` found them all: check
    the probe-line count before reading an absence as a finding.
  - Events name spans and bundles, not values. To follow one value through
    region allocation, log the bundle's values, blocks and preference at
    each `set_reg_allocation` (code-quality-009's `probe_bundle` in
    `unsuccessful/sibling-reg.md`).
  - **Classify by who caused it, not by the symptom.** In code-quality-009,
    "class member found its slot taken" looked like code-quality-002's
    loner problem. Splitting it by *who* held the slot showed 231k of 296k
    weight was another parameter of the same join, colored a moment before
    (`misc/cascade_share.py` there). That split pointed at the fix.
- **Size a remaining cost before choosing the next attempt.** After a kept
  change, `$S/edit_costs.py` on the heaviest inputs shows edit cost by kind
  and loop depth, what deep-loop register moves are for (call arguments,
  parameter registers at jumps, ...), and how much of the reload cost sits
  on latches. It took minutes to rule ideas in or out in code-quality-009.
- **Probe before porting a fix to a sibling code path.** After
  code-quality-009 made edge stores weigh loop depth, the push-up step in
  spill placement still compared frequency only. A probe found it never
  climbs into a deeper block on the 40 heaviest inputs, so changing it
  would be a no-op.

## 4. The loop: one attempt

For each candidate, highest-ranked first:

1. **Re-read the code you are about to change.** Files in this repo are
   edited mid-session by the user and other agents.
2. **Implement it.** Minimal, one idea. `cargo fmt`.
3. **Screen on the targets.** Build to `target/` and run only the targets:

   ```bash
   cargo build --release --example run
   T='(tinygo-regex-0107-u0-99|sqlite3-0226-u0-181|...)'   # targets, guards, canaries
   python3 $S/counts.py -b target/release/examples/run \
       -o /tmp/screen.tsv --only "$T\.postcard\$" <corpora>
   awk -F'\t' -v t="^$T\$" 'NR==1 || $2 ~ t' $R/counts/$base.tsv > /tmp/screen-base.tsv
   python3 $S/diff_counts.py /tmp/screen-base.tsv /tmp/screen.tsv --targets $R/targets.tsv
   ```

   `--only` searches the input's **path**, which ends in `.postcard`, so the
   `$`-anchored names from `targets.tsv` match nothing there; anchor on
   `\.postcard$` instead. The baseline filter matches the TSV's `name`
   column, which has no suffix. Put the guards and the known canaries in
   `T` too: then the screen's gate means something, and a guard that moves
   shows up before the full run. Save the three commands as
   `$R/misc/screen.sh BASE` and rerun it for every variant.

   If the targets do not move, or move the wrong way, rethink before going
   further. Iterating here is cheap.

   **Screen variants of one idea against each other** before committing to
   one. In code-quality-009 the first variant of the kept attempt 1 cost the
   VDBE guard +445; reading the one guard block that regressed showed the
   weighting was wrong, and the fourth variant cost nothing. Record each
   variant's numbers in the attempt's write-up and its patch in
   `$R/patches/`.
4. **Commit** as `WIP: <one line on what it does>`, with a body that sums
   up the attempt's codegen effect (see "Git"), build, and copy to
   `$R/bins/run-<sha>`. If a later variant of the same idea replaces it
   before the decision, `git commit --amend` it: one idea, one commit.
   Remeasure after amending; reuse a TSV only after `cmp`-ing the
   allocation on the targets, since the binary always differs.
5. **Full counts** over every corpus (`counts.py`, as in Setup, into
   `$R/counts/<sha>.tsv`), and diff against the last kept commit:

   ```bash
   python3 $S/diff_counts.py $R/counts/$base.tsv $R/counts/$sha.tsv \
       --targets $R/targets.tsv | tee $R/diffs/<slug>.txt; echo "exit=$?"
   ```

6. **Read the target allocation diff** (an invariant):

   ```bash
   diff -u $R/logs/<target>-$base.txt <($R/bins/run-$sha $A/corpus-X/<target>.postcard) \
       > $R/diffs/<slug>-<target>.diff
   ```

   Walk the hot blocks. Quote the before/after of the hottest one in the
   write-up. Also look at the top few "most regressed" functions
   `diff_counts.py` lists: is each regression an intended trade, or
   collateral damage?

   **For a big function, rank blocks before reading hunks.** A 30,000-line
   diff is unreadable whole. Build `run` in a scratch tree with
   `scripts/block-costs.patch`, dump both sides, and compare:

   ```bash
   for rev in $base $sha; do
       $S/scratch.sh /tmp/bc-$rev $rev
       patch -p1 -d /tmp/bc-$rev < $S/block-costs.patch
       cargo build --release --example run --manifest-path /tmp/bc-$rev/Cargo.toml
       BLOCK_COSTS=1 /tmp/bc-$rev/target/release/examples/run -q <input> \
           2> $R/logs/<target>-$rev-blocks.txt
   done
   python3 $S/block_costs.py $R/logs/<target>-{$base,$sha}-blocks.txt
   ```

   It sums the delta by loop depth and lists the blocks that moved most, so
   the hunks to read, and quote, are the top few of each list. Keep the
   `/tmp/bc-<sha>` builds for the session: every later attempt needs the
   last kept commit's dump, and `edit_costs.py` reads the same dumps.

   **A small guard regression is a lead, not noise.** Read it the same way:
   rank its blocks, then find the decision. In code-quality-009 a +50 on the
   VDBE guard (0.003%) was the *unmatched* parameters' free-list order
   changing because matched ones were assigned in a different order. The
   fix kept the gain and made the guard exactly flat.

   **When a regression is concentrated, bisect it by firing count.** In a
   scratch build, let the new rule fire only for its first `N` occurrences
   (an `AtomicUsize` counter and `std::env::var`, which needs `--features
   std`), and bisect `N` on the regressed input. In code-quality-002 one
   firing of 114 caused 70% of a +7% regression, which turned "the rule is
   wrong" into "the rule is wrong for long bundles".
7. **Correctness**: tests (see "Testing") and, in the background, the
   fuzzer. `counts.py` has already run the checker on every input.
8. **Decide** (see "Decision rule").
   - **Kept**: move `todo/NN-<slug>.md` to `successful/<slug>.md` and fill it
     in; update `report.md`. This commit is the next attempt's baseline, and
     its `counts/<sha>.tsv` is the next baseline TSV.
   - **Dropped**: move it to `unsuccessful/<slug>.md` with the sha, tag the
     commit (`git tag code-quality-NNN/<slug> HEAD`), check `git status` is
     clean, then `git reset --hard HEAD^`. Update `report.md`.
9. **Re-read the analysis's next finding against the new tip.** A kept
   change can fix or move more than its target. Re-run the event tally on
   the next target before starting on it.

Every few kept commits, and always at the end, diff **the original base
against the current tip**. That gives the cumulative result, and it catches
individually-small regressions that add up.

## Decision rule

`diff_counts.py`'s gate encodes the mechanical part. It exits 1 when any
target or guard function's estimated cycles rose, a target lost status `ok`,
any input failed the checker, any corpus's estimated cycles rose more than
`--tolerance` (0.5%), typical-set instructions rose more than
`--insts-budget` (2%), or any input became a compile-time outlier (2x and
over 10⁹ instructions).

| targets' estimated cycles | gate | verdict |
| --- | --- | --- |
| fell | pass | **keep** |
| fell | fails on corpus tolerance or a non-target function | keep **only** if every regressing function is explained by the allocation diff as an intended trade and the corpus totals still fall; write the justification. Otherwise rework or drop |
| fell | fails on a guard | **drop**, or rework so the guard holds |
| fell | fails on compile time | see "Compile-time budget" |
| fell | fails on checker or tests | **drop**. Not negotiable |
| flat or rose | any | **drop**. Not worth the churn, even if a corpus total improved by accident; record what it did |

An attempt whose screen already fails (targets flat or worse, or a
screened corpus well past tolerance) may be dropped **at the screen**,
without full counts, tests or fuzzing. Say so in its write-up, and say which
of steps 5 to 7 were skipped.

An idea rejected **before** implementing, because a probe shows it cannot
move estimated cycles or would only change code size, is not an attempt.
Write it up in `unsuccessful/` anyway, say it was not counted against the
user's attempt budget, and list it in `report.md` below the attempts table.

Also weigh, and record:

- **slots**: a rise in spill slots on targets needs a reason.
- **plain counts vs estimated cycles**: when they disagree, explain which
  blocks the edits moved between.
- **breadth**: "better 40, worse 3" is stronger evidence than one target
  improving.

## Compile-time budget

`counts.py` records instructions retired inside `regicide::run` per input,
from the same run, so every attempt gets a compile-time screen for free.
`diff_counts.py` reports the typical-set total (inputs under 10¹⁰ in the
baseline) and each heavy input.

- **Typical set within 2%**: fine. If it moved by more than ~0.5% either
  way, confirm with the sibling skill's statistics, at `-n 20`, because
  `counts.py` takes one sample:

  ```bash
  python3 .claude/skills/optimize-regicide-compile-time/scripts/compare.py \
      -n 20 $R/bins/run-<base> $R/bins/run-<cand> <set dir>
  ```

  (It exits 2 because the allocation counts differ. That is expected here;
  read its insts verdict.)
- **Over budget**: keep only if the estimated-cycles win is large and broad,
  and say so with both numbers in the write-up.
- **A new heavy outlier** (a superlinear blowup on some input): drop or
  rework. One codegen win cost a function 35 s → 146 s of compile time
  before (known-findings).
- **A uniform jump across every corpus is usually inlining, not your code.**
  In code-quality-003 a spill-placement change cost +8.7% insts on
  `keccak_core`, an input with no cold blocks, all of it inside region
  allocation, which the change did not touch. Removing a check later cost
  +12%, though the code did strictly less work. Both times rustc had stopped
  inlining something hot (`FixedEntitySet::insert`, `coalescing::coalesce`).
  Confirm with the `timing` feature (`RUST_LOG=regicide::timing=trace`) that
  the time moved into an untouched pass. Then find what went out of line:

  ```bash
  norm() { nm -C "$1" | grep -E ' [tT] ' | awk '{$1=$2=""; print}' \
      | sed 's/^ *//' | grep -E '^<?regicide::' | sort -u; }
  comm -3 <(norm $R/bins/run-<base>) <(norm $R/bins/run-<cand>)
  ```

  An `#[inline]` on the function that went out of line fixed both. Bisect
  the edit in a scratch tree first, since a one-line restructuring (a second
  loop over the spans) can be the trigger.

## Testing

```bash
cargo test --all-features > $R/misc/test-<sha>.txt 2>&1; echo "exit=$?"
grep -E '^test result|FAILED|panicked' $R/misc/test-<sha>.txt
```

Check `exit=`, not the grep: when the test build fails to compile there are
no `test result` lines at all, and an empty grep looks like a pass. regicide
has `cfg(test)` struct literals only the test build sees. At `cf70ddd` the
clean baseline was 421 + 8 passed, 10 ignored, about 2 minutes.

**Property tests can encode the rule you are changing.** In
code-quality-009, `spill_placement_properties` checked that an edge store
sits below a *more frequent* predecessor, by `BlockFrequency` alone. Making
spill placement weigh loop depth failed it, correctly. Update such a
property to the new definition, computed independently of the pass (there,
from the region tree's loop depth and `BlockFrequency::estimate_weight`),
and say so in the write-up. Never loosen it to make it pass.

**Fixture tests change with the allocation.** A visualizer fixture test
(`fixtures_are_up_to_date`) fails when allocation changes what it renders.
Re-bless it only after reading its diff (`REGICIDE_BLESS_FIXTURE=1 cargo test
--all-features --lib fixtures_are_up_to_date`). Record why it changed in the
attempt's write-up. Never bless blind. The visualizer's node tests read the
same fixtures, so run them too:

```bash
(cd visualizer && node --test test/) 2>&1 | grep -E '^ℹ (pass|fail)|^✖'
```

The clean baseline is 125 pass, 1 fail ("an event summary names its entities
as clickable parts", a missing `slot=`).

**Some tests pin an allocation shape, not a rendering.** A test that needs a
dead move, a spill in a loop, and so on stops testing anything when a better
allocator stops producing that shape. Do not weaken its assertions. Find a
new input that still has the shape. When hand edits fail, let mutatis search
and shrink: a temporary `Check::new().iters(..).run_with(m::default::<TestInput>(),
crate::test::corpus(), ..)` whose property returns `Err` on the wanted
shape. Print `result.unwrap_err().unwrap_failed().value` with `{:#?}`; the
plain `Debug` of `TestFunction` hides classes and remat costs. Then write it
up as a named `TestInput::with_...` and add it to `corpus()`.

**Fuzz** every kept attempt, in the background while you write up. The user's
notes require `-s none`, libFuzzer flags after `--`, and enough
`-max_total_time` to get past corpus loading (~410 s):

```bash
cargo +nightly fuzz run -s none allocate -- -max_total_time=700 \
    > $R/misc/fuzz-<sha>.log 2>&1; echo "exit=$?"
grep -E 'INITED|DONE|Done [0-9]+ runs|ERROR|panicked' $R/misc/fuzz-<sha>.log
```

Require `INITED` and `Done` before calling it clean. A fuzz crash after a
heuristic change is yours until proven otherwise: soak time on a clean HEAD
cannot classify it as pre-existing. An exit of 144 with no crash in the log
means something outside the session killed the run. Rerun it; it is not a
pass. **Before rerunning, make sure the old run is dead** (`pgrep -fl
'fuzz run'`). In 003 a `pkill` missed it, and both runs wrote into one log,
which then held two `Done` lines for different builds. **Scope every
`pgrep`/`pkill` to this worktree's path** (`pgrep -fl "$PWD/fuzz"`): other
worktrees fuzz at the same time, and in 009 `pkill -f
'fuzz/target.*allocate'` matched another session's run. Prefer waiting for
your own run to finish over killing anything.

Fuzz the commit you keep, not an earlier variant of it: an amended commit is
a different build.

## Sightglass and Wasmtime: only when asked

**Do not build Wasmtime or run sightglass unless the user explicitly asks.**
Estimated cycles are the verdict for this skill. If they ask:

- Inside `~/regalloc2`, use its `wasmtime/` checkout and scripts, as the
  analysis skill does.
- Anywhere else (this worktree), **ask the user how to build it**. Do not
  repoint `~/regalloc2/regicide`; other sessions and skills rely on it.

Otherwise, end the report by recommending the user re-run
`analyze-regicide-codegen` on the tip. Estimated cycles are not a runtime
measurement. The analyses saw instruction deltas overstate cycles ~10x on
small benchmarks, and fan-out understate them, so the runtime verdict belongs
to that step.

## Git

- Work on your own branch (see Setup). **Never push, pull, or fetch.**
- `WIP: <summary>` commit messages, with **no Co-Authored-By or other
  attribution lines** (the user's standing rule for regicide). Stage by
  explicit path (`git add src/foo.rs`), never `git add -A`/`.`: untracked
  files like `visualizer-plans/` must not be committed, and `reports/` is
  ignored anyway.
- **Every `WIP` commit body sums up its codegen effect**, so `git log` alone
  tells the next reader what each commit bought. Write it once the full
  counts are in (amend the commit then), and keep it short:

  ```
  WIP: color a join's spilled parameters heaviest (parameter, slot) pair first

  Parameters of a join were given slots one at a time, so an early one
  could take the slot a later one needed and displace it in turn.

  Estimated cycles vs cf70ddd (codegen-analysis-006 corpora):
  countMatches -18.2%, regexp.compile -5.0%; tinygo-regex -10.4%,
  protobuf -1.6%, hashset -1.0%, sqlite3 -0.3%, others 0.
  Better 59 / worse 0; guards unchanged. countMatches slot-to-slot
  copies 641 -> 42. Compile time -0.5%.
  ```

  One or two sentences on the mechanism, then the targets, the corpora that
  moved, better/worse, guards, the plain-count signature that tells the
  story, and compile time. A dropped attempt's body says why it was dropped
  (its tag keeps it reachable).
- Each dropped attempt: commit it, tag it (`code-quality-NNN/<slug>`), record
  the sha in `unsuccessful/<slug>.md`, then `git reset --hard HEAD^`. The tag
  keeps the sha reachable so the report's reference does not rot. Check
  `git status` is clean before the reset.
- The stash is shared with other worktrees and sessions. Do not use it.
- This skill's instructions to commit **are** the user's explicit request to
  commit for the duration of this work. That overrides the default "never
  commit in regicide" rule only for the `WIP` commits and tags described
  here.
- **If the harness refuses `git commit`** (001's was refused as "Git
  Destructive", 003's `git add` as "Modify Shared Resources"), do not retry
  or work around it. Switch to patches for the
  rest of the session, and say so at the top of `report.md`:
  - `git diff > $R/patches/NN-<slug>.patch` once an attempt is built. Name
    the bin `run-aNN` and the counts `aNN.tsv`, since there is no sha.
  - A dropped attempt: restore the tree to the last kept patch (a saved copy
    of each touched file, or `git apply -R` of the dropped delta), and check
    that `git diff` equals the kept patch.
  - Leave the kept work unstaged, and list the files for the user to commit.
  - The user may stage, commit or rebase while you work (003's tip was
    committed under a new sha mid-session). Run `git status` and `git log -3`
    before each round. Never stage your follow-up edits on top of what they
    staged; an `MM` file in `git status` is the expected state.

## 5. Finish

`report.md` must end with:

- the base and final shas, and the `WIP` commits in order with one-line
  results (check that each kept commit's body carries its codegen summary,
  with the final numbers);
- the **cumulative** base-vs-tip diff: per corpus, and per target and guard,
  in estimated cycles and plain counts, plus the compile-time delta;
- every attempt in a table, kept and dropped, linking to its file;
- **coverage of the analysis**: for each of its "things to fix", whether it
  is addressed, partly addressed, or untouched, and why;
- what is still worth trying, ranked, for the next session;
- the recommendation to re-run `analyze-regicide-codegen` on the tip;
- anything learned that should go into this skill, also in
  `misc/skill-learnings.md`.

Then tell the user where the report is and summarize the cumulative result.

## Pitfalls

- **Judging on plain totals.** Moves deliberately traded into cold blocks
  raise the total and lower the cost. Judge on estimated cycles.
- **Summing over inputs only one side finished.** A timeout on one side faked
  a +29% reload regression in analysis 003. `diff_counts.py` compares only
  inputs `ok` on both sides; keep it that way in any ad hoc arithmetic.
- **Reading a corpus total as a function result.** A corpus is dominated by
  its biggest function. Look at the targets and the per-function lists.
- **Trusting the analysis's mechanism.** Re-derive it from the event counts on
  your base.
- **Hint hit rate without hint width.** A whole-class hint is "honored" by any
  register. Report how many registers each hint allowed.
- **Lifting a cap.** Caps in regicide often bound compile time as a side
  effect. Lifting one improved codegen and cost one function 4x its compile
  time.
- **Comparing estimated cycles across inputs**, or with the analysis skill's
  virtual cycles. It ranks two allocations of the same inputs; nothing more.
- **Changing output-affecting order by accident.** Swapping a `BTreeMap` for
  a hash map changes iteration order, and so decisions. Here that is allowed,
  but it must be the change you meant, visible in the diff and explained.
- **Counting files with `ls | wc -l`.** `ls` columnizes into a pipe on this
  host. Use `ls -1` or `find`.
- **Overriding the split score instead of extending it.** A rule that
  picks its own cut, or prefers a non-middle cut among ties, gives up the
  middle-of-tied-run halving (`a183083`). Long bundles then get peeled at
  an end, and the leftover piece reloads inside a loop. Every such rule in
  code-quality-002 regressed `hashset-0077-u0-72` by 5% to 7%.
- **Backgrounded subshells and inline variables.** In
  `R=... && (cmd $R) & ...`, the subshell may not see `R`; use absolute
  paths in anything run with `&`.
- **A compile-time baseline from before `642668d`.** Split pricing got 38%
  to 92% cheaper there with identical allocation; an older TSV makes every
  candidate look like a compile-time win.
- **Believing a stuck replay is a hang.** Some inputs take minutes (the
  analysis's sqlite3 VDBE function took ~1 minute, some tinygo-regex inputs
  far longer). `counts.py` prints any input over 10 s as it finishes.
- **...or that a stuck replay is slow.** In 001 a `run` child sat in state
  `T` (stopped by something outside the session), and `counts.py`'s timeout
  never fires on a stopped process. If the log stalls on the last few inputs,
  run `ps -o pid,stat,command` on the `run-*` children. Replay the input by
  itself to rule out your change, then `kill -CONT <pid>`.
- **Reading single-sample compile time on a loaded host.** With load
  averages of 15-25, `counts.py`'s insts swung 10% on an *unchanged*
  allocation (switch-0004 in 001's attempt 1). Check `uptime` before reading
  the compile-time section, and confirm any surprise with `compare.py -n 20`.
- **A priority tweak cannot fix a placement problem.** In code-quality-003,
  two cold-region priority tiers were meant to stop spills landing in hot
  blocks. Both were dropped: whichever value a cold block spills, spill
  placement put the store in the hot predecessor. The fix was in spill
  placement. When the cost is *where* an edit lands, look at the pass that
  places it first.
- **"Has a slot" is not "was stored on this path".** A value that already has
  a spill slot can still reach a block in a register, and spilling it there
  needs a new store. 003's attempt 2 assumed otherwise and regressed
  countMatches +1.85%.
- **Comparing `Block::frequency` to find a loop exit.** Cranelift rates every
  block inside a loop NORMAL, the same as the code after it, so a
  frequency-only rule cannot see a loop exit. Use the estimate's own weight,
  `Block::weight` in `region_tree.rs` (frequency weight x 10 per enclosing
  loop), and `Block::runs_more`/`runs_cmp` to compare two blocks: the
  frequency weight saturates at `COLD` and `HOT`, so they break weight ties
  by raw frequency. That one change was code-quality-009's -14% on
  countMatches.
- **Fixing one decision at a time in a pass that makes them in a batch.**
  `enter_block` colored a join's parameters one after another, each taking
  its best free slot. A later parameter that needed that slot more was
  displaced, and displaced the next: five parameters shifted by one slot at
  one depth-4 join. Greedy matching over (weight, parameter, slot) pairs,
  heaviest first, fixed 870 → 70 mismatched pairs in countMatches. Look for
  the same shape wherever a pass assigns a group of things that compete for
  one pool.
- **Biasing the next assignment instead of the decision that caused it.**
  code-quality-009 attempt 3 put a split value's sibling register first in
  an unhinted piece's candidates: regexp.compile +3.9%, and it never fired
  on keccak/blake3's seams, whose pieces are hinted. Seam moves come from
  where the cut went; the fix belongs in the split score.
- **Testing a split heuristic only in `split_into_minimal_or_spill`.** Most
  shredding happens one cut at a time in `split_between_spans`, whose halves
  are requeued. 001's attempt 3 changed only the minimal split and moved
  nothing (122 `BundleSplitIntoMinimal` vs 2,418 `BundleSplitBetweenSpans`
  in countMatches). Tally both events before choosing where to intervene.

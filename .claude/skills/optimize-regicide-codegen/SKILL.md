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
mkdir -p $R/{successful,unsuccessful,todo,counts,diffs,bins,logs,misc}
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
       $A/corpus-* <cited earlier corpora> 2> $R/misc/counts-$sha.log
   ```

   Run it in the background and do "From analysis to backlog" meanwhile.
   Every row must be `ok` or `skipped`; a `failed` row on the untouched tree
   usually means the corpus predates an input-format change, and that corpus
   cannot be used. A `timeout` (default 900 s) marks an input to keep out of
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
   # role	regex (searched in the input's file name)	label
   target	tinygo-regex-0107-u0-99	tinygo countMatches, fix #1
   guard	hashset-0009-u0-8	hashset rehash, preserve #2
   ```

   `diff_counts.py` fails the gate if a regex matches nothing, so a typo
   cannot silently gate nothing.
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

- **Find the hot block in the printout.** Hot means inside the innermost
  loop and not cold. The analysis says which loop; the printout's `-->`
  successor lines give the CFG, so back edges are visible.
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
  you want. It is the cheapest regression guard you can leave behind.

## 4. The loop: one attempt

For each candidate, highest-ranked first:

1. **Re-read the code you are about to change.** Files in this repo are
   edited mid-session by the user and other agents.
2. **Implement it.** Minimal, one idea. `cargo fmt`.
3. **Screen on the targets.** Build to `target/` and run only the targets:

   ```bash
   cargo build --release --example run
   python3 $S/counts.py -b target/release/examples/run \
       -o /tmp/screen.tsv --only '<target regex>' <corpora>
   python3 $S/diff_counts.py <(grep -E '^corpus|<target regex>' $R/counts/$base.tsv) \
       /tmp/screen.tsv --targets $R/targets.tsv
   ```

   Read the targets table and ignore the gate: guards are not in the
   screen, so it fails on them by design. If the targets do not move, or
   move the wrong way, rethink before going further. Iterating here is
   cheap.
4. **Commit** as `WIP: <one line on what it does>` (see "Git"), build, and
   copy to `$R/bins/run-<sha>`.
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

## Testing

```bash
cargo test --all-features > $R/misc/test-<sha>.txt 2>&1; echo "exit=$?"
grep -E '^test result|FAILED|panicked' $R/misc/test-<sha>.txt
```

Check `exit=`, not the grep: when the test build fails to compile there are
no `test result` lines at all, and an empty grep looks like a pass. regicide
has `cfg(test)` struct literals only the test build sees. At `36e91a7` the
clean baseline was 402 + 8 passed, 10 ignored, about 2 minutes.

**Fixture tests change with the allocation.** A visualizer fixture test
(`fixtures_are_up_to_date`) fails when allocation changes what it renders.
Re-bless it only after reading its diff, and record why it changed in the
attempt's write-up; never bless blind.

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
cannot classify it as pre-existing.

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
- Each dropped attempt: commit it, tag it (`code-quality-NNN/<slug>`), record
  the sha in `unsuccessful/<slug>.md`, then `git reset --hard HEAD^`. The tag
  keeps the sha reachable so the report's reference does not rot. Check
  `git status` is clean before the reset.
- The stash is shared with other worktrees and sessions. Do not use it.
- This skill's instructions to commit **are** the user's explicit request to
  commit for the duration of this work. That overrides the default "never
  commit in regicide" rule only for the `WIP` commits and tags described
  here.

## 5. Finish

`report.md` must end with:

- the base and final shas, and the `WIP` commits in order with one-line
  results;
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
- **Believing a stuck replay is a hang.** Some inputs take minutes (the
  analysis's sqlite3 VDBE function took ~1 minute, some tinygo-regex inputs
  far longer). `counts.py` prints any input over 10 s as it finishes.

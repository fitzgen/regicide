# Report templates

Line-wrap markdown at ~80 columns. Every file starts with the date and time
and the sha(s) it describes. Deltas are (candidate - baseline) / baseline:
**negative is better**.

## `report.md`

```markdown
# Regicide code quality NNN

Started: YYYY-MM-DD HH:MM. Last updated: YYYY-MM-DD HH:MM.

## Status

<One or two lines: what is running right now, what is next. Updated after
every step, so that a glance tells the reader where things are.>

## Setup

- Branch `code-quality-NNN`, base `<sha>` (`<subject>`).
- Analysis: `~/regalloc2/reports/codegen-analysis-NNN/` (measured regicide
  `<sha>`). Commits since then that touch the blamed files: <list>.
- Corpora: `<paths>` (N distinct inputs; timeouts excluded: <list>).
- Targets and guards: `targets.tsv` (N targets, M guards).
- In-flight branches touching the same code: <list, and how they relate>.
- Baseline tests: <result>.

## Cumulative result (base `<sha>` vs tip `<sha>`)

| corpus | est. cycles Δ | moves Δ | spills Δ | reloads Δ | slots Δ | insts Δ |
| --- | --- | --- | --- | --- | --- | --- |
| codegen-analysis-003/corpus-keccak | -x.x% | ... | ... | ... | ... | +x.x% |

| role | function | est. cycles base → tip | moves | spills | reloads | slots |
| --- | --- | --- | --- | --- | --- | --- |
| target | tinygo countMatches (fix #1) | 123,456 → 98,765 (-20.0%) | a→b | ... | ... | ... |
| guard | hashset rehash (preserve #2) | unchanged | | | | |

Functions better / worse / unchanged: X / Y / Z. Raw: `diffs/cumulative.txt`.

## Attempts

| # | slug | commit | verdict | target est. Δ | corpora est. Δ | insts Δ | notes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | [callee-saved-order](successful/callee-saved-order.md) | `abc1234` | kept | -3.1% | -0.2%..0% | +0.1% | |
| 2 | [split-move-cost](unsuccessful/split-move-cost.md) | `def5678` (tag) | dropped | +0.4% | | | guard regressed |

## Coverage of the analysis

| finding | status | by |
| --- | --- | --- |
| #1 back-edge reload seams | partly addressed | attempt 3 |
| #2 split scoring | untouched | out of time |

## Backlog

Ranked, with estimated saving and the evidence for each. Link `todo/`.

## Next steps

- Re-run `analyze-regicide-codegen` on tip `<sha>` for the runtime verdict.
- ...
```

## `todo/NN-<slug>.md`

```markdown
# <Title>

YYYY-MM-DD HH:MM. Base `<sha>`.

- **Finding:** #N of codegen-analysis-NNN (<one line>).
- **Mechanism:** what the allocator does, and why, re-derived on the base
  (event tallies in `../logs/`).
- **Targets:** inputs, and the hot block in each.
- **Expected signature:** which events and counts should move.
- **Estimated saving:** in estimated cycles on the targets, with arithmetic.
- **Breadth:** how many corpora / functions show the signature.
- **Idea:** the change, and where in the code.
```

## `successful/<slug>.md` and `unsuccessful/<slug>.md`

```markdown
# <Title>

YYYY-MM-DD HH:MM. Commit `<sha>` (`WIP: ...`), measured against `<base sha>`.
Verdict: kept / dropped (<one-line reason>). Tag (if dropped):
`code-quality-NNN/<slug>`.

## Idea

The finding and mechanism (from `todo/`), with the evidence.

## Change

What the commit does, in a paragraph. Files touched.

## Result

`diff_counts.py` excerpt: the targets table, the per-corpus table, better /
worse / unchanged, the gate. Raw: `../diffs/<slug>.txt`.

## The hot block, before and after

The hottest block of the main target, from `../diffs/<slug>-<target>.diff`,
with one line on each hunk. Say what the hunk means for the generated code
(e.g. "the reload on the back edge is gone; the value now stays in r5 across
the loop").

## Regressions examined

Each function in the "most regressed" list worth a word: intended trade or
collateral damage, and why.

## Correctness

- `counts.py --check`: 0 checker failures over N inputs.
- `cargo test --all-features`: exit 0, N passed. Fixture re-blessed? Why.
- Fuzz: `Done N runs`, no crashes.

## Compile time

Typical-set insts Δ, heavy inputs, and `compare.py` if it was needed.

## Notes

What was learned: why it did not work, what would be needed instead, what it
suggests trying next.
```

# Report templates

Line-wrap markdown at ~80 columns. Every file starts with the date and time
and the sha(s) it describes.

## `report.md`

```markdown
# Regicide compile-time speedups NNN

Started: YYYY-MM-DD HH:MM. Last updated: YYYY-MM-DD HH:MM.

## Status

<One or two lines: what is running right now, what is next. Updated after
every step, so that a glance tells the reader where things are.>

## Setup

- Branch `compile-speedups-NNN`, base `<sha>` (`<subject>`).
- Corpora: `<paths>` (N inputs, M distinct).
- Input sets: `sets/typical` (N inputs, X insts), heavy inputs below.
- Host: <cpu>, load at start <uptime>; see `misc/environment.md`.
- Baseline tests: <result>.

## Cumulative result (base `<sha>` vs tip `<sha>`)

| set | insts Δ (99% CI) | wall Δ (99% CI) | n |
| --- | --- | --- | --- |
| typical | -x.x% [..] | -x.x% [..] | 20 |
| heavy/00-... | ... | ... | 10 |

## Where the time goes (baseline)

<Timing-log pass breakdown and samply top-of-tree, for typical and for the
heaviest input. Link to profiles/.>

## Attempts

| # | slug | commit | verdict | typical insts | typical wall | heavy | notes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | [btree-to-vec](successful/btree-to-vec.md) | `abc1234` | kept | -3.1% | -2.5% | -40% on 00 | |
| 2 | [inline-x](unsuccessful/inline-x.md) | `def5678` (tag) | dropped | +0.0% | n.s. | n.s. | no effect |

## Screened out (no attempt spent)

| # | idea | typical | why |
| --- | --- | ---: | --- |
| 1 | ... | +x.x% | ... (and the null test's reading, if one was run) |

Full write-ups and counters in `misc/screens.md`; diffs beside it.

## Probes

Ceiling probes (delete the work, wrong output) and marginal-cost probes
(do it twice, output unchanged), with what each bounds.

| probe | typical | reading |
| --- | ---: | --- |
| ... | -x.x% | ... |

## Backlog

Ranked, with a measured ceiling where there is one and the profile
evidence for each.

1. ...

## Not yet understood / follow-ups

- ...

## Where the time goes at the tip

The timing-log breakdown over `typical/` at the final sha, so the next
session starts from where this one left the profile rather than re-deriving
it. Take it with the recipe in SKILL.md, "Which pass: the `timing` feature",
and give each pass its share as well as its milliseconds.

| pass | ms | share | vs base |
| --- | ---: | ---: | ---: |
| region allocate | 0000.0 | 00.0% | -0.0pp |
| coalesce | 0000.0 | 00.0% | +0.0pp |
| generate moves | ... | ... | ... |
| live ranges | ... | ... | ... |
| eliminate redundant moves | ... | ... | ... |
| ... | ... | ... | ... |

Note which passes moved and which did not: a pass whose *share* grew while
its milliseconds fell is one the session did not touch, and is usually the
next session's starting point.
```

## `successful/<slug>.md` and `unsuccessful/<slug>.md`

```markdown
# <Title>

YYYY-MM-DD HH:MM. Commit `<sha>` (`WIP: ...`), measured against `<base sha>`.
Verdict: kept / dropped (<one-line reason>). The commit's message body holds
the same per-set result (see SKILL.md, "Git: commit messages").

## Idea

What was slow and why, with evidence: the profile rows (link
`../profiles/...`), the disassembly excerpt that showed the problem, counter
results ("92% of calls see one element").

## Change

What the commit does, in a paragraph. Files touched.

## Correctness

- `cargo test --all-features`: exit 0, N passed.
- `check_identical.sh --check` over typical + <heavy inputs>: identical.
- Fuzz (if run): `Done N runs`, no crashes.

## Measurements

Host load at the time: <uptime>, notable processes.

| set | n | insts Δ (99% CI, p) | wall Δ (99% CI, p) |
| --- | --- | --- | --- |
| typical | 20 | ... | ... |
| heavy/00-... | 10 | ... | ... |

Raw: `../bench/<slug>-*.csv`, `../bench/<slug>-*.txt`.

After profile (if taken): how the hot function's share moved.

## Notes

Anything learned: why it did not work, what would be needed instead, what it
suggests trying next.
```

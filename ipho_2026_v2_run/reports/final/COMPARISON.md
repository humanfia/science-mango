# IPhO 2026 pipeline comparison

Comparison date: 2026-07-27 (UTC)

The primary comparison uses the same 22 theory targets. The six E1
experimental subquestions were explicitly paused in the new run and are
reported separately rather than counted as passes or failures.

| Metric on the common 22 theory targets | Old pipeline | New routing pipeline |
|---|---:|---:|
| Formalization compiled | 22/22 (100.00%) | 22/22 (100.00%) |
| Strict semantic pass | 20/22 (90.91%) | 22/22 (100.00%) |
| Proof Review solved | 20/22 (90.91%) | 22/22 (100.00%) |
| Zero-`sorry` files | 20/22 (90.91%) | 22/22 (100.00%) |

## What changed

- The old run stopped at 20/22 on the theory subset. `1_B_2` and `2_B_1`
  exhausted proof retries under insufficient contracts.
- The new run solved `1_B_2` directly. Proof Review then identified
  `1_C_1` as an underdetermined helper contract and `2_B_1` as an
  answer-bearing assumption, routed both back to formalization, and accepted
  both repaired contracts before proof resumed.
- The final proof gate is 22/22 solved with zero theory `sorry`.

## Full 28-target context

| Checkpoint | Result |
|---|---:|
| Old pipeline proof Review | 25/28 solved |
| Old pipeline zero-`sorry` files | 26/28 |
| Old pipeline semantically unresolved | 3/28 |
| New pipeline active theory scope | 22/22 solved |
| New pipeline experimental scope | 6/6 user-skipped; 17 `sorry` retained |

## Runtime context

| Metric | Old checkpoint | New solved-theory checkpoint |
|---|---:|---:|
| Completed iterations | 100 | 5 |
| Summed iteration wall time | 26045 s (7.23 h) | 7307 s (2.03 h) |
| Input tokens | 17,443,518 | 9,663,624 |
| Output tokens | 1,860,068 | 1,339,129 |
| Agent turns | 5,513 | 3,463 |

The new solved-theory checkpoint used 71.9% less summed wall
time. This resource comparison is contextual: the new run skipped six
experimental targets after their first formalization Review, whereas the old
run continued through 100 iterations and included all 28 targets.

The new run was manually stopped after entering `polish`: its planner proposed
already solved, zero-`sorry` files and validation dropped them all as no-ops.
No proof work remained.

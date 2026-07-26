# Iteration 003 Plan

## Decision made

- Dispatch all 217 final review retries in `physics-formalize` mode. The
  configured 1,000-objective/32-parallel limits support one wave; 170 targets
  chiefly need reports, while nine import and 40 semantic lanes need statement
  work. Expected cost is ~2k–12k Lean LOC plus 217 reports; the risk is using
  the third-review ceiling on heterogeneous repairs. Reverse only if plan
  validation finds a concrete blocked dependency or objective truncation.

## Graph and doctor handling

- Cleared current coverage debt: 527 target pins, 30,539 helper blocks with
  direct source-derived dependencies, and the `hello` scaffold reduced
  unmatched declarations 31,067 → 0. Doctor rerun: no broken/malformed refs;
  only the nine dispatched Mathlib-import blockers remain.
- Thirty-one nodes are genuinely isolated. Retry lanes remove/private any they
  touch; accepted-file cleanup is deferred until after the final gate because
  plan permissions cannot edit Lean and reopening 783 accepted statements for
  cosmetic connectivity is higher risk than tracked post-gate cleanup.

## Tool substitutions

- Run-local role/prompt files remain absent; used the identical-SHA canonical
  archive copies and the project venv Archon executable. No subagents were
  enabled or invoked.

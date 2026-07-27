# Iteration 001 plan

## Decision made

- Dispatch all 28 prepared targets now, one independent `physics-formalize` lane per missing Lean file.
- Reason: the user explicitly requires full first-iteration lane coverage; config sets `max_objectives = 28` and `max_parallel = 28`; the graph exposes all 28 targets with zero infinite-effort holes, broken references, or coverage debt.
- Trade-off: a one-shot ~900–2,800 LOC scaffold wave has more concurrency and contract-review load than the usual ≤10-file batch, but isolates failures per file and directly exercises the benchmark.
- Reverse only if deterministic plan validation reports a concrete source/chapter mismatch or blocked import; do not pre-emptively defer or order siblings.

## Evidence

- Matched sets: 28 objectives, 28 chapters, 28 prepared source reports, 28 absent outputs.
- Source-policy failures: 0. Chapter-gate failures: 0.
- Isolated target nodes are intentional because these outputs have no Lean dependencies; `previous_parts` remains prose context.

## Tool substitutions

- `archon dag-query` was unavailable on `PATH`; used the injected leandag state plus direct source/chapter/output checks.

## Subagent skips

- None enabled; classic single-agent loop requested.

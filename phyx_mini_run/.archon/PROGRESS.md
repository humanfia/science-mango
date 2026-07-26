# Project Progress

## Current Stage

prover

## Stages

- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

*(no prover dispatch this iter — see `iter/iter-042/plan.md` for rationale;
eligible accepted-open target count 0, eligibility shortfall 32)*

## Deferred Repair Queue

- Twenty-four formalization-passed files are `proof_review_exhausted` and must
  never be dispatched again. Nine retain 11 placeholders; the other fifteen
  have no placeholder but still failed proof Review. They require structural
  statement/elaboration repair and a gate reset, not another prover attempt.
- Thirty-seven files remain outside prover dispatch pending genuine current
  grounding evidence. `0117` and `0629` need refreshed reports for their
  symbolic statements; `0206` and `0472` additionally need direct `Mathlib`
  imports through an authorized Lean-writing route. The full sets are in
  `task_pending.md`.
- The `0954` chapter now matches its current symbolic energy/reachability theorem and no longer claims the rejected undefined-\(\sigma\) threshold.
- Twenty-nine declaration-site-only blueprint nodes are confirmed dead and await an authorized Lean structural cleanup; no dependency edges should be fabricated for them.

## Build and Graph State

- Iteration 036 finalized with a successful root `lake build`.
- The formalization gate has 963 passed and 37 exhausted files. Proof Review
  session 41 records 933 solved and 24 exhausted files; six
  previously certified closed files predate proof-gate tracking and have no
  placeholder. No passed, non-exhausted file has a live placeholder, so the
  deterministic eligible set is empty.
- The 143-node ready frontier maps its live placeholders to 39 files: 30 are
  formalization-Review exhausted and nine are proof-Review exhausted. The
  graph has no infinite-effort sources, broken `\uses{}` references, or
  Lean-to-blueprint coverage debt.
- The doctor still reports the known direct-`Mathlib` import blockers on
  `0206` and `0472`; plan cannot edit Lean and subagents are disabled.
- Run-local `.archon/AGENTS.md` and `.archon/prompts/{plan,review}.md` remain absent; the identical-SHA canonical archive files supply the active instructions.

## Preserved Proof State

Proof Review certifies 933 solved files, and six earlier certified files remain
closed outside proof-gate tracking. Forty-six files still contain placeholders:
37 are formalization-Review exhausted and nine are proof-Review exhausted.

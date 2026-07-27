# Iteration 002 plan

## Decision made

- Dispatch the seven Review-rejected files only, all in `physics-formalize`; retain the 21 accepted contracts.
- Repair the four doctor blockers with genuine Physlib quantity carriers/named SI projections.
- For experimental files, prefer derivable symbolic + uncertainty contracts over disconnected fixed reports. Reverse only if Formalization Review shows a source-backed input still missing.

## Evidence

- Iter-001 preflight: 28/28 compile; Formalization Review: 21 pass, 7 fail.
- Official sources re-read: T2 pages 2/4; E1 problem pages 7--9, 12--13; E1 solution pages 1, 2, and 6.
- Disproof/reconciliation: A.1's printed mass and amount uncertainty conflict by factors of ten with its volume and molecule count. C.6's printed `10⁻⁵` slope conflicts with both the raw-table regression and stated resistance; `10⁻³` is consistent.
- Added unique blueprint pins for all 587 physics declarations; no duplicate labels or broken `\uses`.

## Tool substitutions

- `archon dag-query` is unavailable; used injected leandag state plus direct declaration/pin checks.

## Subagent skips

- None enabled; classic single-agent loop requested.

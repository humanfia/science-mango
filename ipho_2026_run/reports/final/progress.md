# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

(no prover dispatch this iter — see `iter/iter-100/plan.md` for rationale; all three unresolved targets are proof-Review-exhausted and require user-authored contract revision)

## Mechanical Gate

- 25 of 28 targets have passed proof Review.
- `1_B_2` and `2_B_1` retain the project's only two sorries, both under contracts shown insufficient by three reviewed attempts.
- `4_B_6` is placeholder-free but failed semantic Review because its conclusion does not encode uncertainty propagation.
- The faithfulness rule forbids agents from strengthening these signatures or hypotheses merely to obtain proofs, so none is a valid prover-mode objective under the current contract.

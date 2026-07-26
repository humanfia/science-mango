# Prover result: `problem_phyx_mini_0285.lean`

## Outcome

Closed `rounded_width_is_thirty_nine_seats` without changing its signature.
The proof projects the supplied dimensionful speed and width laws to their
real-valued readouts, substitutes the problem data, and applies
`round_eq_iff`.  The resulting exact width is
`(853 / 39) * (9 / 5) = 2559 / 65`, which lies in `[38.5, 39.5)`.

There are no remaining `sorry` placeholders in the assigned file.

## Verification

- Lean language-server diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0285.lean`: exit code 0.
- Root `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, `sorryAx`, or added `axiom`.
- `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`: clean.

## Blueprint marker

The statement and proof environments for
`PhyXMiniProblems.ProblemPhyXMini0285.rounded_width_is_thirty_nine_seats`
are ready for `\leanok`.  I did not edit the blueprint because the prover's
explicit write permissions restrict this lane to its assigned Lean file and
this task-result file; the project's deterministic marker sync owns that edit.

## Redraft needed

None.

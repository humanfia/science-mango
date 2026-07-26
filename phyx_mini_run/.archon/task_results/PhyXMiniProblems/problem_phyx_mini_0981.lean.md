# Prover result: `problem_phyx_mini_0981.lean`

## Status

Complete. The sole `sorry` in
`terminal_bar_thermal_power_matches_answer_B` was replaced by a proof, with the
declaration signature unchanged.

## Proof

Terminal zero acceleration and Newton's second law give equality of magnetic
drag and the downslope gravitational force. The magnetic-drag law and the
normal-field geometry then yield

`I L B cos φ = m g sin φ`.

Positivity of the length and applied field gives their nonvanishing, while
positivity of the normal field together with `B_normal = B cos φ` gives
`cos φ ≠ 0`. Dividing the force balance therefore gives

`I = m g tan φ / (L B)`.

Substitution into the independent Joule-heating law `P = I² R` proves the
stated answer-B formula.

## Verification

- Direct Lean compilation with the project's existing Lake module search path
  exited with status 0 and no diagnostics:
  `lean -T1 PhyXMiniProblems/problem_phyx_mini_0981.lean`.
- Source audit found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- No redraft is needed.

## Blueprint

The target theorem environment still needs `\leanok`. It was not edited here
because the prover task's explicit write permissions restrict changes to the
assigned Lean file and this task-result file.

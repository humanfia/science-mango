# Prover result: `problem_phyx_mini_0403.lean`

## Outcome

Completed both declarations in
`PhyXMiniProblems/problem_phyx_mini_0403.lean` without changing either
signature:

- `workDoneByGas_eq_eighty_joules`
- `workDoneOnGas_eq_negative_eighty_joules`

The intermediate lemma converts the figure readouts to SI values:
`400 kPa = 400000 Pa`, `100 cm³ = 1 / 10000 m³`, and
`300 cm³ = 3 / 10000 m³`.  Substitution into the supplied isobaric boundary
work law gives `400000 * (3 / 10000 - 1 / 10000) = 80`.  The target theorem
then uses the supplied work-on-gas sign convention to conclude `-80 J`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0403.lean` completed
  successfully with no diagnostics.
- The assigned file contains no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- No statement redraft is needed.
- The existing `/- USER: ... -/` comment was read and preserved.

## Project notes

- `.archon/AGENTS.md` was absent at the required path.  The available
  `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, injected prover
  instructions, source report, grounding report, and blueprint chapter were
  used.
- The blueprint proof environments were not marked `\leanok` because the
  task's explicit write-permission clause permits changes only to the assigned
  Lean file and this task-result file and separately says not to edit the
  blueprint chapter.  The plan/orchestration stage should synchronize
  `\leanok` for the now-verified lemma and theorem.

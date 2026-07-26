# Prover result: `problem_phyx_mini_0409.lean`

## Outcome

Completed both proof obligations in
`PhyXMiniProblems/problem_phyx_mini_0409.lean` without changing either
declaration signature:

- `processB_heat_exact`
- `heat_required_for_process_B_is_answer_C`

The intermediate lemma converts the primary figure readouts to coherent SI
values:

- `2 atm = 202650 Pa`;
- `1000 cm³ = 1 / 1000 m³`;
- `3000 cm³ = 3 / 1000 m³`.

It then specializes the supplied ideal-gas equation, diatomic internal-energy
law, isobaric boundary-work law, and first law to process `B`. Exact nonlinear
arithmetic gives
`Q_B = 28371 / 20 J = 1418.55 J`.

The target theorem reuses that exact result, proves it is within `50 J` of the
displayed `1400 J`, and checks every constructor of `AnswerChoice` to show
that answer C is uniquely closest.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0409.lean` completed
  successfully with no diagnostics.
- `lake build` completed successfully with 4 jobs.
- Axiom/source verification of both declarations reported only Lean's
  standard `propext`, `Classical.choice`, and `Quot.sound`, with no source
  warnings.
- The assigned file contains no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- The existing `/- USER: ... -/` comment was read and preserved.

## Project notes

- The requested `.archon/AGENTS.md` is absent. The injected prover
  instructions, `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`,
  linked source report, grounding report, references summary, and blueprint
  chapter were used.
- The advertised `archon` executable was unavailable on `PATH`, so the
  optional dependency-graph query could not run.
- The blueprint environments for `processB_heat_exact` and
  `heat_required_for_process_B_is_answer_C` are ready for `\leanok`
  synchronization. The blueprint was not edited because the task's explicit
  write-permission clause permits changes only to the assigned Lean file and
  this task-result file.

## Redraft needed

None.

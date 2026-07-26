# Prover result: `problem_phyx_mini_0193.lean`

## Outcome

- Proved `frontWavelength_formula` by dividing the forward wavefront-spacing
  law by the strictly positive emitted frequency.
- Proved `frontWavelength_matches_recordedAnswerA` by deriving the
  air-relative source speed `30 m/s`, substituting the `340 m/s`, `30 m/s`,
  and `300 Hz` readouts, and checking that the resulting exact wavelength
  `31/30 m` lies within `0.005 m` of answer A's `1.03 m`.
- No declaration signature or physical assumption was changed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0193.lean` succeeded.
- Lean LSP diagnostics are empty.
- The assigned file contains no `sorry`, `admit`, `axiom`, or `sorryAx`.
- `lean_verify` reports only the standard `propext`, `Classical.choice`, and
  `Quot.sound` dependencies, with no source-scan warnings.

## Blueprint markers

The completed lemma and theorem are ready for `\leanok` synchronization. The
prover did not edit the blueprint because the active write permissions allow
changes only to the assigned Lean file and this task-result file.

## Workflow note

The requested `.archon/AGENTS.md` is absent, as also recorded in
`.archon/PROGRESS.md`. The available physics prover instructions were followed.
The file-specific `USER` comment only records that the Lean source did not
exist when autoformalization began.

## Redraft needed

None.

# Prover result: `problem_phyx_mini_0492.lean`

## Status

- Closed `totalWorkDoneByGas_matches_recordedAnswerD`.
- No `sorry`, `admit`, new axioms, or proof escape hatches remain.
- The declaration signature was not changed.

## Proof summary

- Reduced one litre-atmosphere to exactly `101325 / 1000` joules using
  Physlib's definitions of `DimPressure.standardAtmosphere` and
  `DimPressure.pascal`.
- Applied the supplied boundary-work laws to prove that the constant-volume
  leg contributes zero work and that the constant-pressure leg contributes
  `1.4 * (9.3 - 5.9) * 101.325 = 482.307` joules.
- Used the supplied total-work sum law, verified that `482.307` lies within
  five joules of the displayed `480 J`, and checked all four constructors of
  `AnswerChoice` to prove that recorded choice `D` is unique.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0492.lean` exited `0`.
- Lean LSP diagnostics are empty.
- Axiom/source verification found only the standard foundations `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious source patterns.
- The corresponding blueprint theorem proof environment is ready for
  `\leanok`; the blueprint was not edited because prover write permissions
  make it read-only and marker synchronization is coordinator-managed.

## Redraft needed

None.

## Environment note

The run-local `.archon/AGENTS.md` is absent. The canonical archived role
instructions for this project, the run-local `PROGRESS.md`, and the supplied
physics prover instructions were read instead.

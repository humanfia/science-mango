# PhyXMiniProblems/problem_phyx_mini_0534.lean

## transmittedToIncidentWaveNumberRatio (line 260)

### Attempt 1

- **Approach:** Substitute the figure's `110`- and `154`-pixel arrow spans into the linear calibration law to derive `7(E-U)=2E`. Apply this relation to the two regional dispersion equations, cancel the positive squared Planck action, and prove that the positive wave-number ratio is the positive square root of `2/7`.
- **Result:** RESOLVED.
- **Key insight:** Positivity of both wave numbers selects `Real.sqrt (2/7)` from the equality of squares.
- **Proof body:** 1 line (`sorry`) before; 90 lines after.

## transmissionProbabilityForFigurePotentialStep (line 362)

### Attempt 1

- **Approach:** Use `transmittedToIncidentWaveNumberRatio` and positivity of the incident wave number to rewrite `k₂ = sqrt(2/7) * k₁`, then cancel `k₁` in the flux coefficient. Bound the radical between exact rational values, obtaining `363/400 < T ≤ 227/250`; use this bracket to prove three-decimal agreement with `0.908` and compare choice D against every answer choice.
- **Result:** RESOLVED.
- **Key insight:** The same rigorous bracket proves both the rounding claim and all four nearest-choice cases without decimal approximation tactics.
- **Proof body:** 1 line (`sorry`) before; 136 lines after.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0534.lean` completed successfully with no output.
- Source scan found no `sorry`, `admit`, declared axiom, `sorryAx`, or `native_decide`.
- `lean_verify` reported no warnings for either declaration. The only dependencies listed were Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`; no axioms were introduced by this file.

## Blueprint status

- The lemma and theorem blueprint environments are ready for `\leanok`.
- I did not edit the blueprint because this prover task explicitly restricts writes to the assigned Lean file and this task-result file.

## Summary

- Sorry count: **2 → 0**.
- Closed: `transmittedToIncidentWaveNumberRatio`.
- Closed: `transmissionProbabilityForFigurePotentialStep`.
- Still open: none.
- Adjacent sorries: none remained in the assigned file.
- New declarations needing blueprint entries: none.
- Redraft needed: no.

## Why I stopped

Real progress: closed both assigned sorries, reduced the file's sorry count from 2 to 0, and verified that the complete file compiles.

## Environment note

- The requested `.archon/AGENTS.md` file was absent from the project state directory. I followed `.archon/PROGRESS.md`, `.archon/prover-modes/physics.md`, the assigned blueprint chapter, and the explicit instructions in the objective.

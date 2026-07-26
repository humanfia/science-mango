# Result: `problem_phyx_mini_0715.lean`

## Status

Complete. Both proof placeholders were replaced by honest proofs without
changing any declaration signature.

## Proof summary

- `initialSpeeds_eq_modelPredictions` expands kinetic energy, each gravitational
  potential, and mechanical-energy conservation. Positivity of the satellite
  mass permits cancellation, after which exact ring arithmetic gives the two
  squared-speed formulas. Nonnegativity of Physlib speed readouts selects the
  appropriate square roots.
- The target theorem derives the exact metre readouts from the given kilometre
  readouts using the `Dimensionful.property` coherence law.
- Substitution of the Earth calibration and boundary data gives exact squared
  initial speeds
  `51675283720 / 6771` for the spherical model and `8095320` for the flat
  model.
- Exact rational square comparisons prove the flat speed is between
  `1.0299` and `1.03` times the spherical speed. This yields
  `2.99% < error < 3%`.
- Since every displayed percentage is at most D's `2.7%` and the error exceeds
  `2.99%`, D is at least as close as every displayed option.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0715.lean` exited with code
  0. Its only output was the expected unused-variable warnings for the frozen
  `hScenario` and `hFigure` parameters.
- Lean axiom/source scans for both proved declarations reported only
  `propext`, `Classical.choice`, and `Quot.sound`, with no suspicious source
  patterns.
- The assigned Lean file contains no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.

## Notes

- `.archon/AGENTS.md` is absent in this run, so
  `.archon/prover-modes/physics.md` supplied the available role instructions.
- The blueprint chapter was read, but its target environment contains the
  autoformalization placeholder rather than an informal proof. I did not add
  `\leanok` because the explicit prover write permissions allow edits only to
  the assigned Lean file and this task-result file.

## Redraft needed

None.

# Prover result — Archon iteration 014

## Outcome

- Closed all three proof obligations in
  `PhyXMiniProblems/problem_phyx_mini_0187.lean`.
- Preserved every declaration signature and physical hypothesis.
- No redraft is needed.

## Proof summary

- `principal_design_is_quarter_wavelength_and_phase` bounds the town-side
  interference order using the positive principal phase and the positive
  sub-half-wavelength propagation phase.  Integer arithmetic forces that
  order to be zero.  The analogous country-side bounds force its odd
  half-turn order to be one.  The two interference equations then give
  separation `wavelength / 4` and initial phase `π / 2`.
- `broadcast_delay_is_quarter_period` combines that quarter-turn phase with
  the unit-covariant delay/phase law.  The frequency-period law proves that
  the period readout in the selected unit is nonzero, allowing exact
  cancellation and yielding `delay = period / 4`.
- `problem_phyx_mini_0187` specializes `f T = 1` to millisecond readouts.
  The stated `1000 kHz` frequency gives a period of `1/1000 ms`, hence a
  delay of `1/4000 ms`.  The proof derives the exact
  `nanosecond readout = 1000000 * millisecond readout` relation from
  Physlib's `Dimensionful` unit-scaling property, obtaining `250 ns` and
  recorded choice D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0187.lean` succeeds.
  Its only diagnostic is the frozen unused `hfigure` hypothesis in the final
  theorem.
- Source audit found no `sorry`, `admit`, introduced `axiom`,
  `native_decide`, or `sorryAx` mechanism.
- `lean_verify` reports no suspicious source patterns.  The final theorem
  depends only on the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The assigned file contains no `/- USER: ... -/` hint.

## Project metadata

- The requested `.archon/AGENTS.md` is absent in this checkout; the available
  `.archon/prover-modes/physics.md`, `PROGRESS.md`, blueprint chapter, and
  source report were read and followed.
- The advertised `archon` executable is not available on `PATH`, so the
  optional DAG query could not run.
- The proved blueprint environments are ready for `\leanok`.  The blueprint
  was not edited because prover write permissions restrict changes to the
  assigned Lean file and this task-result file.

## Redraft needed

None.

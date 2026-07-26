# Prover result: `problem_phyx_mini_0120.lean`

## Status

Partial, with three of four declarations soundly closed. The file compiles.
The only remaining `sorry` is the numerical equality inside
`problem_phyx_mini_0120`; the source supplies no numerical value for
`R`, `lambda`, `d`, or their ratio.

Iteration 016 retry: the partial proof now rewrites the requested distance by
the proved symbolic formula before the remaining `sorry`. The exact open goal
is therefore the unsupported calibration `R * lambda / d = 13 / 4`. Closing
that goal via the inconsistency of the overbroad screen law would prove an
arbitrary dataset answer by explosion, so it is not a faithful repair.

## Proofs completed

- `resultantElectricFieldAtP`
  - Rewrote coherent superposition with the three harmonic-component laws.
  - Expanded `cos (x + phi)` and `cos (x - phi)` and normalized the resulting
    identity by ring arithmetic.
- `closestAbsoluteMaximum_phase_eq_two_pi`
  - Proved millimeter readouts are `1000` times meter readouts from the
    `Dimensionful` unit-coherence property.
  - Used positivity and the screen-projection law to show the selected
    positive maximum has positive phase.
  - Compared its irradiance with the central point and used
    `-1 <= cos phase <= 1` to derive `cos phase = 1`.
  - Constructed the first positive `2 * pi` offset, proved it is an absolute
    maximum, and applied the closest-positive condition.
  - Used `Real.cos_eq_one_iff` to identify the positive integer recurrence
    number as exactly one.
- `closestAbsoluteMaximumDistance_formula`
  - Substituted the proved phase `2 * pi` into the phase-difference law.
  - Cancelled the positive wavelength, slit separation, and `2 * pi` factors
    to obtain `sin theta = lambda / d`.
  - Combined this with the screen-projection law and converted consistent
    meter readouts to millimeter readouts, proving the symbolic distance
    `R * lambda / d`.
- `problem_phyx_mini_0120` (partial)
  - The symbolic formula conjunct is discharged by the preceding lemma.
  - Once the remaining numerical equality is available, the proof already
    verifies that choice A matches and that B, C, and D cannot match.
  - The numerical subproof explicitly rewrites the distance using
    `closestAbsoluteMaximumDistance_formula`.
  - The remaining gap is focused at
    `lengthInMillimeters setup.screenDistanceR *
    lengthInMillimeters setup.wavelengthLambda /
    lengthInMillimeters setup.slitSeparationD = 13 / 4`.

No declaration signature, hypothesis, conclusion, definition, or import was
changed.

## Verification

- Iteration 016 reran
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0120.lean`; it succeeds.
- Diagnostics contain one expected `declaration uses sorry` warning for the
  main theorem and one harmless unused-variable warning for `h_figure`.
- Source scan finds one `sorry` and no `admit`, `axiom`, `native_decide`, or
  `sorryAx`.
- Iteration 016 `lean_verify` checks of all three closed declarations report
  no suspicious source patterns and only the standard imported axioms
  `propext`, `Classical.choice`, and `Quot.sound`.

## Redraft needed

### Unsupported numerical conclusion

- Original problem: `phyx_mini_0120`.
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0120.source.json`.
- Theorem: `PhyXMiniProblems.ProblemPhyXMini0120.problem_phyx_mini_0120`.
- Blocker: the hypotheses determine only the symbolic distance
  `R * lambda / d`. The source image contains no numerical readout for
  `R`, `lambda`, `d`, or `R * lambda / d`, so they do not entail
  `13 / 4 mm` or the recorded choice A.
- Smallest faithful statement change: make the main theorem conclude only the
  symbolic formula. If the dataset answer must remain a theorem conclusion,
  add an independently sourced calibration premise giving
  `lengthInMillimeters R * lengthInMillimeters lambda /
  lengthInMillimeters d = 13 / 4`.

### Overbroad screen law

- Theorem affected:
  `PhyXMiniProblems.ProblemPhyXMini0120.closestAbsoluteMaximum_phase_eq_two_pi`.
- `screenProjectionLaw` currently quantifies over every `LengthQuantity`.
  Since `sin` is bounded while length offsets are unbounded, this law is
  inconsistent with positive finite screen distance. An ex-falso proof of
  the missing numerical result is therefore technically possible but would
  be physically unfaithful and was deliberately not used.
- Smallest model change: quantify the projection, phase, and intensity laws
  over a reachable-screen-offset subtype or predicate, and explicitly state
  reachability of the first-order offset `R * lambda / d`.

## Project metadata notes

- The requested `.archon/AGENTS.md` is absent in this checkout. I followed the
  explicit task instructions and `.archon/prover-modes/physics.md`.
- The assigned Lean file contains no `/- USER: ... -/` comment.
- The blueprint was not edited because the task explicitly restricts writes
  to the assigned Lean file and this task-result file. An authorized
  blueprint editor should add `\leanok` to the environments for the three
  completed lemmas; the main target must remain unmarked.

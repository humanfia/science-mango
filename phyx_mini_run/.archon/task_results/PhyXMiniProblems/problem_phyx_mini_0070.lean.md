# Prover result: `problem_phyx_mini_0070.lean`

## Status

Complete. Both proof obligations are closed with the original declaration
signatures unchanged:

- `sightlineBottomRun_centimeter_relation`
- `problem_phyx_mini_0070`

This iteration also repairs the proof-review evidence mismatch: the previous
file at this required nested path was the stale autoformalization report and
incorrectly claimed that two `sorry` bodies remained.

## Proof summary

- Specialized `ObeysStraightSightlineGeometry` to centimeters and rewrote the
  independent figure readouts to derive
  `run_cm * tan (π / 6) = 50`.
- Rewrote `tan (π / 6)` to `1 / sqrt 3`.
- Proved `sqrt 3 ≠ 0` from positivity and isolated denominator cancellation in
  a separate equality, giving `run_cm = 50 * sqrt 3` without mutating the
  governing relation with an in-place `field_simp`.
- Used `(sqrt 3)^2 = 3` to certify the rational bounds
  `1.73 < sqrt 3 < 1.75`, hence `86.5 < run_cm < 87.5`.
- Unfolded the absolute-error rounding predicate to prove that the intersection
  rounds to `87 cm`, then reduced answer choice `C` to the same result.

The frozen `physical : HasDepictedPhysicalConfiguration setup` premise is not
needed once the exact figure readouts and straight-sightline equation are
available; it remains in the theorem signature unchanged.

## Faithfulness

The proof derives the numerical run from the general unit-covariant
straight-sightline law and the independent `50 cm`, `30°` figure readouts. No
premise stores the requested `87 cm` result. The answer-choice definition is
used only after the physical readout has been shown to lie strictly between
`86.5 cm` and `87.5 cm`.

The primary image places the displayed angle below a horizontal reference, so
the derived value is `50 sqrt 3 ≈ 86.6 cm`, matching choice C. The auxiliary
caption's vertical-angle wording conflicts with that primary evidence and with
the recorded answer.

## Verification

- Lean LSP diagnostics: no errors; only the unused-variable linter warning for
  the frozen `physical` theorem parameter.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0070.lean`: exit status 0.
- `lake build`: completed successfully with 4 jobs.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- `lean_verify` for the target reports only Lean's standard foundational
  axioms `propext`, `Classical.choice`, and `Quot.sound`, with no suspicious
  source patterns.
- `git diff --check`: no whitespace errors.

## Blueprint readiness

The lemma and theorem environments are ready for deterministic `\leanok`
synchronization. The blueprint was not edited because the prover write boundary
permits edits only to the assigned Lean file and this result file.

## Redraft needed

None.

## Role-instruction note

The requested `.archon/AGENTS.md` is absent in this checkout, as recorded in
project progress. The user-provided prover contract and
`.archon/prover-modes/physics.md` were followed. The file-specific
`/- USER: ... -/` comment only records that the Lean source did not exist at
autoformalization start and supplies no additional proof hint.

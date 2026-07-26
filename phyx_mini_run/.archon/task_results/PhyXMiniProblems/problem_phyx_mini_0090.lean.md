# Prover result (Archon iteration 014)

## Status

Complete. The assigned Lean file contains proof-closed bodies for all four
declarations:

- `normalizedRayPathLengths`
- `pathDifferenceInWavelengths_eq`
- `phaseDifferenceAtP_eq`
- `problem_phyx_mini_0090`

No `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide` remains in the
assigned file. The frozen declaration signatures were not changed.

This retry required no Lean-source edit: the iteration-013 proof review found
the source compiling, faithful, and proof-complete, but returned `partial`
because this task-result file was stale and still claimed that four `sorry`s
remained. This report replaces that stale evidence with the current verified
state.

## Proof summary

- `normalizedRayPathLengths` specializes the depicted coordinates, the
  readouts `d = yₚ = 6λ` and `D = 20λ`, and the Euclidean-distance law. It
  derives the normalized ray lengths `√712` and `√436`.
- `pathDifferenceInWavelengths_eq` cancels the positive wavelength readout and
  obtains the exact path difference `√712 - √436` wavelengths.
- `phaseDifferenceAtP_eq` combines the equal initial phases with the
  source-by-source monochromatic propagation law, yielding the corresponding
  `Real.Angle` value `2π(√712 - √436)`.
- `problem_phyx_mini_0090` proves certified rational bounds on both square
  roots, traps the exact path difference between `5.8` and `5.9`, and checks
  all four displayed alternatives to show that choice C (`5.80λ`) is nearest.
  The answer choice is derived rather than assumed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0090.lean` exits
  successfully with no output.
- Lean LSP diagnostics report success with no errors, warnings, or failed
  dependencies.
- `lean_verify` reports no suspicious source patterns. The target theorem uses
  only the standard imported axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- A source audit finds zero occurrences of `sorry`, `admit`, `axiom`,
  `sorryAx`, and `native_decide`.

## Blueprint handoff

The proof-closed lemma and theorem environments are ready for `\leanok`.
The blueprint was not edited because this prover lane permits writes only to
the assigned Lean file and this result file.

## Redraft needed

None.

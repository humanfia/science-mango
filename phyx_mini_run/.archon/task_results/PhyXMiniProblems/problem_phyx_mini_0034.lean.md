# Prover result: `problem_phyx_mini_0034.lean`

## Status

Complete. All four `sorry` placeholders were replaced by sound proofs, and the
assigned Lean file compiles.

## Proof summary

- `directPathDistances_eq`: extracted the positive direct object distance from
  the figure ordering, substituted the `10 cm` lens focal length and signed
  magnification `-3/2`, and solved the Gaussian-imaging and magnification
  equations to obtain `p = 50/3` and `q = 25`.
- `mirrorIntermediateImage_coincides_with_object`: used coincidence of the two
  final image positions and the reflected lens Gaussian law to obtain the same
  reflected object distance `50/3`. Equality of the centimeter readouts was
  lifted to equality of `OpticalLength` values via `Dimensionful.ext`, the
  unit-scaling property, and `WithDim.ext`.
- `mirrorFocalLength_eq`: combined the `40 cm` mirror--lens separation with the
  direct object distance to derive equal mirror object and image distances
  `70/3`; the mirror Gaussian law then gives `f = 35/3`.
- `problem_phyx_mini_0034`: applied `mirrorFocalLength_eq` and verified by exact
  rational arithmetic that `35/3 cm` is within `1/20 cm` of answer D's
  `117/10 cm`.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0034.lean`: succeeded.
- Source scan found no `sorry`, `admit`, `sorryAx`, introduced `axiom`, or
  `native_decide`.
- `lean_verify` on
  `PhyXMiniProblems.ProblemPhyXMini0034.problem_phyx_mini_0034` reported only
  the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`,
  with no suspicious-source warnings.
- The compiler reports only three unused-hypothesis linter warnings for
  `h_mirror_magnification`, `h_reflected_lens_magnification`, and
  `h_composition`. Their signatures are frozen, and the stronger hypotheses
  are unnecessary for this proof route.

## Redraft needed

None.

## Blueprint synchronization

The corresponding declarations are proof-closed and ready for `\leanok`
synchronization. The blueprint chapter was not edited because the prover-mode
write permissions explicitly restrict changes to the assigned Lean file and
this task-result file.

## Environment note

The requested run-local `.archon/AGENTS.md` is absent, as already documented in
`.archon/PROGRESS.md`. The canonical `.archon/prover-modes/physics.md`
instructions were followed.

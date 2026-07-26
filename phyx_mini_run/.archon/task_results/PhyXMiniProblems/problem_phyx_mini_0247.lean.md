# Prover result: `problem_phyx_mini_0247.lean`

## Status

Complete. The sole `sorry` in
`PhyXMiniProblems.ProblemPhyXMini0247.problem_phyx_mini_0247` was replaced by
an honest proof without changing the declaration signature.

## Proof summary

- The controlled far-field remainder bound reduces in SI units to
  `|remainder| ≤ 169 / 120`.
- The geometry law then gives
  `0.999 < lengthInMeters setup.pathDifferenceAtP < 1.001`.
- The first-maximum phase condition, wavelength positivity, and
  `Real.pi_pos` give `wavelength = 2 * pathDifference`, hence
  `1.998 < wavelength < 2.002` meters.
- Physlib's `DimSpeed.speedOfLight_in_SI` reduces the propagation speed to
  `299792458 m/s`. Together with `v = wavelength * frequency`, the preceding
  bounds imply `149500000 Hz < frequency < 150500000 Hz`.
- Thus both coherent transmitters round to choice A (`150 MHz`). Case analysis
  on the other labels rules out `100 MHz`, `200 MHz`, and `120 MHz`, proving
  uniqueness.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0247.lean` succeeds.
- `lake build` succeeds (`Build completed successfully (4 jobs)`).
- LSP diagnostics contain no errors and no `declaration uses sorry` warning.
  The only diagnostics are unused-variable linter warnings for `hFigure`,
  `hGuidance`, and `hPathDifference`; their presence in the frozen signature
  is physically descriptive but they are not needed for the numerical
  consequence.
- Source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- The axiom check reports only the standard `propext`, `Classical.choice`, and
  `Quot.sound`.

## Blueprint readiness

The proof block for
`thm:physics:phyx_mini_0247:target` is ready for project-managed `\leanok`
synchronization. The blueprint was not edited because prover permissions make
it read-only.

## Redraft needed

None.

# Prover result: `problem_IPhO_2026_4_A_5.lean`

## Outcome

Closed the sole placeholder in
`IPhO2026Problems.IPhO_2026_4_A_5.target` without changing its signature.
Sorry count: **1 → 0**.

The proof constructs the dimensionful inverse-temperature coefficient whose SI
readout is `1 / 273.15`. From the common positive slope supplied by
`PreviousPartA3Linearity`, it rewrites the measured pressure difference as the
slope times the temperature difference. The nonzero-temperature-change
hypothesis then gives
`(1 / P₀) * (ΔP / ΔT) = 1 / T₀ = 1 / 273.15`. Exact rational normalization
proves both requested uncertainty bounds.

The stronger ideal-gas and experimental-procedure hypotheses are not needed
once the previous-part proportionality conclusion is supplied directly.

## Verification

- Lean language-server diagnostics: no errors or warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_A_5.lean`: exit code 0.
- `lake build`: completed successfully.
- Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, or
  `sorryAx`-style escape hatch.
- Axiom verification reports only Lean/Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint status

The target theorem environment
`thm:physics:IPhO_2026_4_A_5:target` is ready for deterministic `\leanok`
synchronization. The blueprint was not edited because prover permissions make
it read-only.

The chapter exists, but its target proof block still contains generic
autoformalization-task prose rather than the intended informal mathematical
proof. A plan/review pass should replace that prose with the slope-cancellation
argument summarized above.

## Redraft needed

None.

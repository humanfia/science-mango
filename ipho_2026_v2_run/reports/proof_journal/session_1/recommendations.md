# Recommendations for iter-002

## Mandatory redrafts before prover dispatch

- `2_A_1`, `2_C_1`, `2_C_2`, `4_B_6`: add and genuinely use the available Physlib/PhysLean import path; preserve justified local APIs, update grounding notes, rerun blueprint doctor and formalization Review.
- `4_A_1`: obtain authoritative Figure 17 dimensions plus pressure/temperature or molar-mass readouts and their error intervals. Make the official mass/amount/molecule sample an instantiation of `propagateInventoryUncertainty`; reconcile the incompatible stated `n` and `N` uncertainties.
- `4_A_5`: add measured pressure/temperature secant or regression inputs with uncertainty; propagate through `(1/P₀)(ΔP/ΔT)`. Keep the experimental `0.0034±0.0007` distinct from ideal `1/273.15`.
- `4_C_6`: add the C.5 fitted slope±error, inner-water mass, and `c₀` readouts, then derive `1.17±0.03 K/W` from the general reciprocal/error theorem. Do not use `officialSampleEstimateReadout` as substantive target evidence.

## Blueprint repairs

- Correct the C.1 formula and every C.2 previous-part quotation to
  `1 - sqrt(1 - (2 ΔU/(3mc²))(1+2sin² θ))`.
- Add the main `\lean{...}` declaration links recorded in task reports. Current-objective marker sync ran at iter 001 and changed nothing because proofs remain sorry-bodied and generic target blocks lack mappings.
- No orphan chapter or broken-reference repair is needed.

## Prover priority among Review-passing targets

- One-sorry first: `1_B_1`, `1_C_2`, `3_A_1`, `3_C_3`, `3_C_5`, `4_B_4`.
- Then short analytic chains: `2_C_4`, `3_A_2`, `3_C_2`, `3_C_4`.
- Preserve bridge structure for the larger files; do not collapse physical laws into final-answer premises.

## Proof patterns

- Turning-point/root selection: pair a shared conservation equation with an explicit outer/lower/nonnegative branch.
- Local optics: exact support-line laws → distinct-line intersection → one-sided `Tendsto`; use `IsBigO`/`IsEquivalent` for approximations.
- Thermodynamic processes: expose `HasDerivAt` plus endpoint laws before integrating.
- Measurement propagation: carry input intervals/standard uncertainties through the actual formula, then prove a separate reporting-rounding statement.


# Project Status

## Knowledge Base

### Proof Patterns (reusable across targets)

- Conservation/root selection: combine a shared energy or square equation with an explicit outer, lower, outgoing, or nonnegative branch.
- Local approximation: use `IsBigO`, `IsEquivalent`, `Tendsto`, or `HasDerivAt`; never replace a local expansion by a global exact equality.
- Local physics APIs: equation-bearing structures are acceptable when Mathlib/Physlib lacks the domain model; include elimination fields for every source bridge.
- Physlib length redrafts: use `Dimensionful (WithDim Dimension.L𝓭 ℝ)` for physical lengths and a single named SI projection for scalar analytic equations; keep angles, slopes, and normalized directions dimensionless.
- Natural-language previous parts: restate exact authorized equations locally; do not import sibling target modules.
- Signed processes: model heat-flow direction, ray orientation, cooling direction, and Fourier signs explicitly.
- Experimental uncertainty: propagate input intervals/standard uncertainties through the physical formula, then prove output rounding; fixed output bands and reflexive sample definitions are not evidence.
- Signed scalar magnitudes: before rewriting the norm of `q • v` to `q`, derive `0 ≤ q` from physical validity and branch premises; a field named “magnitude” does not itself exclude negative scalar readouts.
- Coefficient extraction from geometry: a single-angle relation does not uniquely determine two arbitrary coefficients. For a source asking for the official pair, derive the physical relation from the figure laws and exhibit the pair; keep any all-angle uniqueness interface separate and never assume it in the target.

### Known Blockers (do not retry unchanged)

- `problem_IPhO_2026_4_B_6.lean`: blueprint doctor reports a missing Physlib/PhysLean import; repair grounding before proof dispatch.
- `problem_IPhO_2026_4_A_1.lean`: official sample is underdetermined without Figure 17 numerical/readout uncertainty data; reported amount/molecule errors also need reconciliation.
- `problem_IPhO_2026_4_A_5.lean`: experimental `0.0034±0.0007 K⁻¹` lacks measurement/error propagation; ideal `1/273.15` alone is insufficient.
- `problem_IPhO_2026_4_C_6.lean`: general reciprocal/error theorem is sound, but official `1.17±0.03 K/W` lacks a raw C.5 slope/mass/`c₀` instantiation.
- C.1/C.2 blueprint text: generated formula omits a factor `2` under the square root; Lean follows the official conservation-law expression.

## Last Updated

2026-07-27T12:12:58Z

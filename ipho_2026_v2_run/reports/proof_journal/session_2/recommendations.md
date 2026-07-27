# Recommendations for iter-003

## Current objectives

All three bounded formal statements pass Review and may move to proof work without another modeling redraft. Proof completion is still required:

1. Prioritize `2_C_2` because only `rayB_firstOrderExpansion` remains open. Combine the eventual angle and exact-coefficient equations, then use Mathlib analytic/Taylor machinery to prove the two `O(Δθ²)` remainders. Keep the SI projection and do not weaken the remainder rate.
2. For `2_A_1`, first prove the closure division and complementary-angle algebra, then use `Real.sin_pi_div_two_sub` for the sine/cosine bridge and assemble the main theorem from `limiting_ray_geometry`.
3. For `2_C_1`, expand the vector reflection law componentwise, establish the doubled-angle direction, use the acute-angle bounds to justify slope division, and derive the intercept from point-line incidence.

Do not replace any current exact law, signed branch, dimensionful carrier, named SI projection, or local asymptotic statement with a bare-real/global-equality shortcut.

## Blueprint documentation

- Add dedicated declaration blocks and dependency links for the current targets' Physlib length carriers and named SI projections (`LengthQuantity` with `siLengthValue`, `lengthInMetres`, or `lengthSI`).
- Preserve the existing target `\lean{...}` mappings and let deterministic marker synchronization manage `\leanok`.

## Global doctor carry-over

The following doctor findings are outside this bounded target set and were not semantically reviewed here, but they still prevent a whole-project completion claim:

- `problem_IPhO_2026_4_B_6.lean`: `missing-physlib-import` — “physics target does not import Physlib/PhysLean; attempted grounding should use the available formal physics library before introducing local abstractions”.
- Two malformed bare-label annotations remain in the out-of-scope `1_C_1` and `3_C_5` blueprint chapters; replace the prose labels with valid `\cref{...}` references or human-readable numbers.

Rerun the deterministic doctor after those separate repairs. No orphan-chapter or broken-reference repair is currently indicated.

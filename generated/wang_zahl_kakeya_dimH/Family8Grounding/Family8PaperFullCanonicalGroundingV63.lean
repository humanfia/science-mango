import Family8Grounding.Family8PaperFullCanonicalGroundingV62
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9

/-!
# Full canonical paper-strength Family 8 grounding bundle, V63

This checkpoint integrates the quantitative selected-parent plank geometry
with the canonical V62 chain.  Unit-ball support bounds every side of the
common winning-hull John frame by `2304`.  After the common scalar contraction
by `r`, the inverse map is `6912 / r`-Lipschitz, so the transported tube inner
ball gives every actual long-axis-relabeled side the explicit positive floor
`r * rho / 3456`.

Together with the existing upper bound `1728 * r`, the three-coordinate
dyadic side labels occupy at most
`((ceil (logb 2 (5971968 / rho)) + 1).toNat) ^ 3` buckets.  The common factor
`r` cancels exactly, yielding an explicit `O(log(1/rho)^3)` weighted-retention
loss while preserving the two genuinely anisotropic transverse parameters in
the resulting actual `IsPlank 576 a b` family.  For admissible actual tube
data, unit-ball support is supplied directly by admissibility rather than by
a new side-floor or operator-norm premise.

This checkpoint does not yet prove the certified-plank Córdoba estimate or
the remaining paper-strength Lemma 5.11 inputs.  The one-step
self-improvement and `mainLemmaOne` therefore also remain open.
-/

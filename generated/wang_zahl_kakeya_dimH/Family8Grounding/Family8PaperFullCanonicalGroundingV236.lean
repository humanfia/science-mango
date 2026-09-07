import Family8Grounding.Family8PaperFullCanonicalGroundingV235
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV2

/-!
# Family 8 full canonical grounding checkpoint V236

The actual adaptive flat alternative is now expressed entirely in powers of
the original fine scale.  For nonnegative `tau`, the certified dichotomy is

`a <= rho^(1-tau)` or
`adaptiveScale <= max
  (191102976 * (286654464 * delta^((epsilon*(1-epsilon))*tau)))
  (31104 * delta^(epsilon^2))`.

Thus the geometric `rho^tau` transport has disappeared from the remaining
interface.  The flat branch now needs only an explicit small-scale threshold
absorbing these constants and a compatible positive scale exponent.
-/

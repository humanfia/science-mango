import Family8Grounding.Family8PaperFullCanonicalGroundingV230
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV1

/-!
# Family 8 full canonical grounding checkpoint V231

The actual maximum-density hull thin/flat dichotomy now controls the genuine
adaptive scale in the flat branch.  For the canonical buffered radius `rho`
and the shortest John axis `a`, the certified alternative is

`a <= rho^(1-tau)` or
`adaptiveScale <= max (191102976 * (286654464 * rho^tau))
                         (31104 * delta^(epsilon^2))`.

This is produced from the selected parent/hull geometry, not supplied as a
flatness callback.  The remaining numerical task is to turn the `rho^tau`
term into the required `delta` power along the identified long interval and
absorb the displayed constants.
-/

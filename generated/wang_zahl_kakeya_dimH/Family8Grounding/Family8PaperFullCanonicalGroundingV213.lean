import Family8Grounding.Family8PaperFullCanonicalGroundingV212
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV8

/-!
# Family 8 full canonical grounding checkpoint V213

The actual long-interval hierarchy now absorbs the centered adaptive scale's
radius-floor component:

`radiusFloor <= 31104 * delta^(epsilon^2)`.

This uses the improved `delta / rho` estimate and the repository's genuine
lower bound for the canonical buffered radius.  The only unclosed component
of this adaptive maximum is therefore the occupied bucket short-side
flatness estimate.  The remaining global seams are unchanged from V212.
-/

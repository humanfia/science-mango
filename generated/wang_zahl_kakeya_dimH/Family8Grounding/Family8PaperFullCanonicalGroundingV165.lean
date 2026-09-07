import Family8Grounding.Family8PaperFullCanonicalGroundingV164
import Family8Grounding.Family8ThinPlankFiveParameterMidpointDirectionPackingV3
import Family8Grounding.Family8CanonicalGlobalOuterScaleCountIdentityV1

/-!
# Family 8 full canonical grounding checkpoint V165

This checkpoint adds two safe interfaces needed by the remaining canonical
composition.  First, the five-parameter packing kernel now consumes the
literal midpoint and normalized-direction coordinates of the actual tubes;
it does not assume containment of a full thick tube, or of the unit extension
of a contracted affine segment, in an anisotropically thin parent box.
Second, the literal global `rho`--`X` middle factor is identified with the
existing loss-free Section 8 scale-count factor.

The remaining substantive seam is to produce the midpoint/direction bounds
and essential-distinctness (or an equivalent affine-overlap packing bound)
for one selected contracted-John fibre.  The outer grouped frozen endpoint
and final same-object telescoping are not claimed here.
-/

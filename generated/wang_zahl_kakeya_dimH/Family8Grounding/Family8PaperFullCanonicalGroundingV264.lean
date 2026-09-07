import Family8Grounding.Family8PaperFullCanonicalGroundingV263
import Family8Grounding.Family8PaperEq45CommonWitnessQuadraticInnerV1
import Family8Grounding.Family8PlankRetainedOwnerFullBallNormalizationV1

/-!
# Family 8 full canonical grounding checkpoint V264

Two independent seams advance here.

First, the actual source-index cardinality supplies a completely constructed
quadratic natural cap for every V13 isotropic common-witness inner factor.
This closes the formal `hinner` interface without a callback.  The cap is an
explicit coarse fallback of order `N^2`; it is retained for correctness and
diagnostics, not substituted for the paper-sharp adaptive bucket estimate.

Second, the retained-owner local dense-ball estimate is normalized to the
full radius-`rho` ball.  Exact three-dimensional ball scaling and the
certified plank cross-section give

`density * a * b * volume (ball 0 rho)`
`  <= 54000 * comparisonConstant^3 * loss * localMass`.

The remaining retained-owner work is to instantiate the paper density and
logarithmic loss, absorb this finite constant into the designated small-scale
power, and regroup the actual final coarse balls into the canonical slab
incidence family used by Family 6.
-/

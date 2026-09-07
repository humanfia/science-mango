import Family8Grounding.Family8PaperFullCanonicalGroundingV264
import Family8Grounding.Family8PaperEq45MaxWitnessSelectedBucketUpperV1
import Family8Grounding.Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV17

/-!
# Family 8 full canonical grounding checkpoint V265

The paper-sharp Eq. (45)--(46) route now uses one literal bucket selected by
the actual `MassPopular` selector.  On that same `(parent, label)` object,
`Family8PaperEq45MaxWitnessSelectedBucketUpperV1` supplies the Eq. (45)
source-average upper estimate and V17 composes it with the adaptive Eq. (46)
inner count.

The resulting bound retains the genuine occupied-bucket witness and the
explicit factor

`((fibreCardCap * conflictLoss) * fibreCardCap) *`
`  globalCap ^ (1 - beta / 2)`.

No multiplicity callback is introduced.  The two remaining inputs on this
edge are exactly the scalar scale absorption for every occupied selected
bucket and the already isolated local `MassPopularCrossEq46Budget` residual.
The quadratic common-witness estimate imported through V264 remains only as
a coarse, independently verified fallback.
-/

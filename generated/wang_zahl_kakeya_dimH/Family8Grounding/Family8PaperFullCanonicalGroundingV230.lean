import Family8Grounding.Family8PaperFullCanonicalGroundingV229
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1

/-!
# Family 8 full canonical grounding checkpoint V230

The paper thin/flat dichotomy is now produced from the actual maximum-density
hull.  Writing `a` for the shortest side of its genuine John frame, every
actual bucket member satisfies the stronger ratio estimate
`bucketShortA <= 286654464 * rho / a`; consequently, for every `tau`,

`a <= rho^(1-tau)  or  bucketShortA <= 286654464 * rho^tau`.

The proof runs through the actual tube carrier, a centered transverse slab,
the member John box, and the certified fine-label transport.  It is not a
generic flatness callback and it supersedes the earlier formal no-go for the
weaker bucket hypotheses alone.
-/

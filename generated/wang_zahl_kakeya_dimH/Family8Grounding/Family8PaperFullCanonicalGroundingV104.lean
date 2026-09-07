import Family8Grounding.Family8PaperFullCanonicalGroundingV103
import Family8Grounding.Family8StickySelectedFineDenseFiberV1
import Family8Grounding.Family8FrozenOuterThirdBaseExponentChoiceV1
import Family8Grounding.Family8CanonicalBufferedFrozenOuterBaseScalarV2

/-!
# Family 8 full canonical grounding checkpoint V104

This import-only checkpoint extends V103 with two audited closures.

* On the literal retained-index subtype cover, a genuinely occupied parent
  fibre is selected with no loss.  The selected global shading density is
  bounded by that same fibre's source density, and its shaded union has
  positive volume.
* The third outer base exponent is now chosen explicitly.  Its long-scale
  gain is exactly the fixed-conflict and native Katz--Tao power cost, so the
  canonical base-scalar theorem no longer accepts scale or exponent-budget
  callbacks.

Failed predecessor drafts are intentionally not imported.
-/

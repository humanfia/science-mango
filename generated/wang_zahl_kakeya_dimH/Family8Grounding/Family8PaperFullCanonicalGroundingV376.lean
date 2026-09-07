import Family8Grounding.Family8PaperFullCanonicalGroundingV375
import Family8Grounding.Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3
import Family8Grounding.Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketActualBridgeV1

/-!
# Family 8 full canonical grounding checkpoint V376

* The endpoint full-refinement long witness now has one packaged producer for
  all proof-dependent buffered-input side conditions: epsilon half, full fine
  nonemptiness, actual active mass positivity, and canonical radius half.
* Both fine and branch shading-aware discrete source budgets are now available
  for the exact selected partition.
* The vertical graph-c bucket is identified with the native
  `actualProjectedTubeCBucket` object expected by the Family 7 high branch.

All imported endpoints have exact builds and only the standard Lean axioms.
-/

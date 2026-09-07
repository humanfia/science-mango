import Family8Grounding.Family8PaperFullCanonicalGroundingV580
import Family8Grounding.Family8CertifiedPlankIntersectingNearParallelRowV1
import Family8Grounding.Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1

/-!
# Full canonical grounding interface checkpoint V581

The large-width branch now has both its sharp local geometric row input and
its weakest faithful fixed-witness consumer.

For an actually intersecting projectively near-parallel plank row, the new
Appendix-B.2 container has side vector `[8 * theta, 4, 4]` and exact volume
`128 * theta`.  Katz--Tao nonconcentration therefore bounds the labelled row
body mass directly, without a global hull or any memberwise carrier floor.

At the other end, a single whole-cross weighted-overlap inequality is now
enough to construct the auxiliary overlap factor and the exact joint budget
consumed by the Equation-(32) endpoint.  The public seam no longer demands a
stronger common residual factorization.

The dyadic Appendix-B.3 aggregation and its final small-power scalar payment
are still required.  Family 7 also still needs the common-choice selector and
its downstream refinement adapter.  No Family 8 closure is claimed here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV581

#print axioms
  Family8CertifiedPlankIntersectingNearParallelRowV1.body_subset_certifiedPlankNearParallelTestBox
#print axioms
  Family8CertifiedPlankIntersectingNearParallelRowV1.sum_body_volume_intersectingNearParallelRow_le
#print axioms
  Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1.WinnerSideLargeBWeightedOverlapWholeCrossPaymentAt
#print axioms
  Family8WinnerSideJointBucketLargeBWeightedOverlapCrossConsumerV1.winnerSide_largeB_weightedOverlap_productAtFixedW_of_wholeCrossPayment

end Family8PaperFullCanonicalGroundingV581

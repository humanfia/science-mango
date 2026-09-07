import Family8Grounding.Family8PaperFullCanonicalGroundingV529
import Family8Grounding.Family8GreedyWinnerNormalizationScalarBoundsV1
import Family8Grounding.Family8GreedySuppliedCoverJointStickyScaleCoverV1

/-!
# Full canonical grounding checkpoint V530

The common normalization used for the selected greedy winners now has a
fully quantitative original-scale range.  A captured actual unit tube and
Parseval force the relabeled long John side to be strictly larger than
`1/2`.  The exact dyadic label then gives a common long endpoint in
`[1, 1024]`, and hence a normalization scalar in `[1/1024, 1]`.

Independently, a greedy occurrence partition and a genuine supplied
`TubeScaleCover` now admit an honest common refinement.  Its occupied coarse
codes remember both the greedy occurrence and the supplied parent, while its
actual coarse tube is exactly the supplied parent tube.  The resulting
`StickyScaleCover` has literal carrier containment and at most `active.card`
coarse occurrences.

These two outputs isolate the remaining geometric seam.  The joint
refinement can split a whole greedy block, so its fibers do not automatically
inherit the whole block's maximal-density or Frostman conclusion.  Conversely,
the scalar bounds alone do not pull a normalized unit-length tube back to one
unit-length tube in the original coordinates.  A compatible fiberwise greedy
construction or a bounded longitudinal decomposition is still required.
Consequently this checkpoint does not claim an unconditional LongCore, DSO,
`mainLemmaOne`, or the full paper theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV530

open Family8GreedyWinnerNormalizationScalarBoundsV1
open Family8GreedySuppliedCoverJointStickyScaleCoverV1

#print axioms exists_half_lt_boxSide_of_unitTube_subset
#print axioms half_lt_winnerLongSide_two
#print axioms one_le_sideShapeUpper_two_of_mem_winnerSideBucket
#print axioms sideShapeUpper_two_le_1024_of_mem_winnerSideBucket
#print axioms winnerBucket_normalizationScalar_bounds
#print axioms
  Family8GreedyWinnerNormalizationScalarBoundsV1.GreedyWinnerNormalizedPlankBucket.normalizationScalar_bounds

#print axioms greedySuppliedJointStickyScaleCover
#print axioms parent_decodes_jointCode
#print axioms fine_mem_decoded_greedyBlock
#print axioms parent_tube_eq_suppliedParentTube
#print axioms fine_carrier_subset_joint_parent
#print axioms occupiedJointParents_card_le_active
#print axioms occupiedJointParents_card_le_blocks_mul_count

end Family8PaperFullCanonicalGroundingV530

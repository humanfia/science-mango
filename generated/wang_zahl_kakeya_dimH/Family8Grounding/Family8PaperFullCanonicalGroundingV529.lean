import Family8Grounding.Family8PaperFullCanonicalGroundingV528
import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8GreedyWinnerNormalizedPlankBucketV1
import Family8Grounding.Family8EpsilonExtremalActiveStickyXUpperV1

/-!
# Full canonical grounding checkpoint V529

For a generic full-convex greedy occurrence partition, every nonempty winner
block now automatically supplies an actual fine-tube witness and hence a
positive comparison-`288` John box.  Its long-axis relabeling has every side
in `[2 * delta, 576]` under unit-ball support.  Honest finite dyadic selections
retain either block mass or occurrence count, with the explicit cubic side
bucket loss.

The mass-retaining side bucket also admits one transverse relabeling and one
positive scalar dilation determined by the common bucket label.  In that one
common normalized coordinate system, all selected winner bodies carry
transported box certificates and are uniform `576`-planks with the same two
short widths.  This is a statement about the commonly transformed winner
family, not yet a sticky cover of the original fine tubes.

Independently, the scale covers supplied by an
`EpsilonExtremalTubeFamily` now restrict to the literal active subtype and
pass through the occupied-parent adapter to genuine `StickyScaleCover`s.
They retain the original parent-tube provenance, satisfy the active coarse
cardinality bound, and obey the literal
`activeCoarseCardScaleMass <= 1024 * coarseDeltaMax` upper bound.

The remaining seam is the pullback from the normalized winner bodies and
normalized fine tubes to an honest unit-length cover in the original
coordinates.  A maximal-density or biased-score guarantee would also require
an additional argument when demanded by a downstream consumer; the supplied
epsilon-extremal covers do not assert either property or strict nonidentity
merging.  Consequently this checkpoint does not claim the full paper theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV529

open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8EpsilonExtremalActiveStickyXUpperV1

#print axioms winnerWitness_tube_subset
#print axioms winnerJohnCertificate
#print axioms two_mul_delta_le_winnerLongSide
#print axioms winnerLongSide_le_576
#print axioms exists_winnerSideBucket_blockMass_retention
#print axioms exists_winnerSideBucket_card_retention

#print axioms normalizedWinnerCertificate
#print axioms GreedyWinnerNormalizedPlankBucket.family_isPlank
#print axioms exists_greedyWinnerNormalizedPlankBucket

#print axioms activeSubtypeDatum_isAdmissible
#print axioms exists_activeStickyCover_with_coarseDeltaMax_XUpper

end Family8PaperFullCanonicalGroundingV529

import Family8Grounding.Family8PaperFullCanonicalGroundingV537
import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5

/-!
# Full canonical grounding interface checkpoint V538

This additive checkpoint records the datum-level target-loss successor to the
V537 all-gamma merge.

The common consumer no longer quantifies over an externally supplied
normalized LongCore witness and consumes `DividingScaleOutput` directly at
`targetEpsilon`.  The high card-large provider may choose an additional
positive terminal scale, which the merge intersects with the automatic
high-gamma threshold.  The complementary card-small branch and both
target-loss monotonicity steps are closed internally.

This remains a conditional interface checkpoint.  It does not instantiate
the all-low-gamma datum provider or the high-gamma card-large analytic
provider, and therefore does not claim an unconditional Family 8 conclusion.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV538

#print axioms
  Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2.mainLemmaOne_of_selectedTrueSplitEtaHDatumDSOProvider
#print axioms
  Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5.selectedTrueSplitEta_hDatumDSO_of_lowGammaLocalCapContext
#print axioms
  Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5.AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer
#print axioms
  Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5.selectedTrueSplitEta_hDatumDSO_of_highGammaCardLargeTargetDSO
#print axioms
  Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5.mainLemmaOne_of_allGammaSelectedTrueSplitEtaDatumBranchProviders

end Family8PaperFullCanonicalGroundingV538

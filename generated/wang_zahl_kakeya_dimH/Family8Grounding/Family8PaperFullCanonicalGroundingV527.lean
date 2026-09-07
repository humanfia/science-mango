import Family8Grounding.Family8PaperFullCanonicalGroundingV526
import Family8Grounding.Family8CellularActualDyadicRegularizationV1
import Family8Grounding.Family8CellularPositiveGraphActualRegularizationV1
import Family8Grounding.Family8CellularJointPointwiseP3P5BridgeV1
import Family8Grounding.Family8ActiveCoarseDeltaMaxXUpperV1

/-!
# Full canonical grounding checkpoint V527

This checkpoint removes the supplied-label seam from cellular REG1/R2.  A
finite nonempty graph with positive finite edge weights now produces a
strictly positive factor-two edge-weight band, followed by a genuinely
right-saturated factor-two right-degree band, with explicit logarithmic
losses.  Positive source shading on the real half-open grid supplies all
finiteness and nonemptiness hypotheses automatically.

On the same cell family and edge set, the J1 band transfers pointwise to the
selected child shading (P3), parent-region multiplicity is exactly the right
degree (P4), and total child multiplicity has the required `4 * mu * d`
upper bound (P5).  The literal upper inequality
`X <= 1024 * coarseDeltaMax` is also recorded for any supplied genuine
sticky cover; it does not construct that cover.

A single existential composer packaging J1 and REG into one output, and the
maximal-density nonidentity `b`-cover itself, remain to be constructed.  No
unconditional LongCore, DSO, or `mainLemmaOne` claim is made here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV527

open Family8CellularActualDyadicRegularizationV1
open Family8CellularPositiveGraphActualRegularizationV1
open Family8CellularJointPointwiseP3P5BridgeV1
open Family8ActiveCoarseDeltaMaxXUpperV1

#print axioms exists_actualDyadicRegularization
#print axioms exists_positiveGraph_actualDyadicRegularization
#print axioms source_shadingMass_le_actualLoss_nsmul_final_shadingMass
#print axioms selectedChildShading_parentLocalFiberMultiplicity_positiveBand
#print axioms parentRegionMultiplicity_eq_rightDegree_of_mem_cell
#print axioms selectedChildShading_pointMultiplicity_lt_four_mul
#print axioms activeCoarseCardScaleMass_le_1024_mul_coarseDeltaMax

end Family8PaperFullCanonicalGroundingV527

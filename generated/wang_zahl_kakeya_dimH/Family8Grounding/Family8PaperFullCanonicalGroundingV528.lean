import Family8Grounding.Family8PaperFullCanonicalGroundingV527
import Family8Grounding.Family8CellularJointFactoringComposerV1
import Family8Grounding.Family8CellularUnitPartitionJointFactoringComposerV1
import Family8Grounding.Family8TubeScaleCoverOccupiedStickyAdapterV1
import Family8Grounding.Family8GreedyPlankCertifiedStickyScaleCoverV1

/-!
# Full canonical grounding checkpoint V528

This checkpoint packages the cellular construction into one honest
existential witness.  From positive shading mass and finite cell coverage it
automatically chooses repair J1, builds the genuine positive parent--cell
graph, applies numeric REG1/REG2, and exposes P1--P5 for one common final edge
set.  Its unit-partition specialization discharges cell coverage from
closed-unit-ball support using the genuine half-open Mathlib grid.

On the sticky-cover side, a supplied `TubeScaleCover` now gives a literal
occupied `StickyScaleCover`, with optional deletion and canonical reindexing
of unused coarse codes.  Separately, a genuine greedy occurrence partition
together with supplied plank certificates for all winners gives a certified
long-tube `StickyScaleCover`.  Thus supplied covers, and supplied certified
winner data which actually merge siblings, retain their nonidentity parent
structure in the constructed sticky cover.

The certificates for greedy winners are still an explicit callback.  Their
automatic construction, including a uniform common-scalar pullback, and the
resulting unconditional maximal-density certified cover existence remain
open.  Consequently this checkpoint does not claim an unconditional
LongCore, DSO, `mainLemmaOne`, or the full paper theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV528

open Family8CellularJointFactoringComposerV1
open Family8CellularUnitPartitionJointFactoringComposerV1
open Family8TubeScaleCoverOccupiedStickyAdapterV1
open Family8GreedyPlankCertifiedStickyScaleCoverV1

#print axioms exists_cellularJointFactoringWitness
#print axioms parentRegionMultiplicity_positiveBand_of_mem_parentRegions
#print axioms selectedChildShading_pointMultiplicity_lt_four_mul_of_mem_shadedUnion
#print axioms exists_unitPartitionJointFactoringWitness
#print axioms ofTubeScaleCover
#print axioms compactActiveSubtypeScaleCover
#print axioms compactActiveSubtypeScaleCover_parent_tube
#print axioms greedyPlankCertifiedStickyScaleCover
#print axioms fine_carrier_subset_parent_tube
#print axioms exists_fullGreedyCertifiedStickyScaleCover

end Family8PaperFullCanonicalGroundingV528

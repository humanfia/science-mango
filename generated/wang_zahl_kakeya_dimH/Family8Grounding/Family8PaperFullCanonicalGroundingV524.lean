import Family8Grounding.Family8PaperFullCanonicalGroundingV523
import Family8Grounding.Family8CellularPositiveParentCellEdgeMassV1

/-!
# Full canonical grounding checkpoint V524

This checkpoint constructs the positive source parent--cell graph from the
genuine half-open cells of V523.  The complete graph has total weight equal
to the source shading mass, deleting exactly its zero-weight edges preserves
that total, and the child shading selected by the resulting positive graph
therefore retains the full source mass.  The unit-partition specialization
uses only closed-unit-ball support of the source carriers.

Quantitative mass retention after two-stage regularization and the
maximal-density nonidentity `b`-cover remain to be connected.  Consequently
this checkpoint makes no unconditional LongCore, DSO, or `mainLemmaOne`
claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV524

open Family8CellularPositiveParentCellEdgeMassV1

#print axioms positiveWeightedCellularEdges
#print axioms edgeWeight_allParentCellEdges_eq_shadingMass
#print axioms edgeWeight_positiveParentCellEdges_eq_allParentCellEdges
#print axioms selectedChildShading_positiveParentCellEdges_shadingMass_eq
#print axioms unitPartition_positiveParentCellEdges_edgeWeight_eq_shadingMass
#print axioms unitPartition_selectedChildShading_positive_shadingMass_eq

end Family8PaperFullCanonicalGroundingV524

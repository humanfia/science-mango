import Family8Grounding.Family8PaperFullCanonicalGroundingV524
import Family8Grounding.Family8CellularRegularizedShadingMassP1V1
import Family8Grounding.Family8CellularPositiveRegularizedP1V1

/-!
# Full canonical grounding checkpoint V525

This checkpoint connects the positive source graph of V524 to the final
edge set of two-stage weighted regularization.  The exact edge/shading mass
identity yields P1 relative to the original source shading, with the product
of the two explicit finite label counts as loss.  It also exposes the
factor-two whole-incidence variants based on retained edge cardinality or
equal-volume labelled-parent mass.

The numerical dyadic semantics of the supplied labels, the common inner
multiplicity selection needed for P3, and the maximal-density nonidentity
`b`-cover are not claimed here.  Hence this checkpoint makes no
unconditional LongCore, DSO, or `mainLemmaOne` claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV525

open Family8CellularRegularizedShadingMassP1V1
open Family8CellularPositiveRegularizedP1V1

#print axioms source_shadingMass_le_labelLoss_nsmul_final_shadingMass
#print axioms cardFraction_mul_source_shadingMass_le_final_shadingMass
#print axioms labelledParentMassFraction_mul_source_shadingMass_le_final_shadingMass
#print axioms source_shadingMass_le_labelLoss_nsmul_positiveRegularized
#print axioms exists_positiveRegularization_with_sourceMass_le
#print axioms
  exists_unitPartition_positiveRegularization_with_sourceMass_le

end Family8PaperFullCanonicalGroundingV525

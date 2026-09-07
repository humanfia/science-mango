import Family8Grounding.Family8PaperFullCanonicalGroundingV521
import Family8Grounding.Family8FrozenAssemblyImmediateJointP1P5V1
import Family8Grounding.Family8CellularEqualVolumeEdgeMassV1
import Family8Grounding.Family8CellularJointFactoringFiniteCoreV1
import Family8Grounding.Family8CellularJointFactoringRegularizationV1

/-!
# Full canonical grounding checkpoint V522

This checkpoint adds the finite, incidence-faithful core of repaired
cellular joint factoring:

* the immediate P1--P5 consequences already available from a frozen
  assembly, explicitly separated from the stronger cellular statement;
* equal-volume spatial cell bookkeeping and labelled parent-mass formulas;
* P2, right-saturated P4, P5, and factor-two whole-incidence lifting on one
  finite parent--cell edge set; and
* an actual two-stage weighted REG1/R2 selection producing the saturated
  edge set with explicit finite loss.

The half-open cell geometry, the positive source edge graph, and the
maximal-density nonidentity `b`-cover are still geometric outputs to be
constructed.  This checkpoint therefore makes no unconditional LongCore,
DSO, or `mainLemmaOne` claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8PaperFullCanonicalGroundingV522

open Family8FrozenAssemblyImmediateJointP1P5V1
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointFactoringRegularizationV1

#print axioms immediateJointP1P5_of_assembly
#print axioms EqualVolumeCells.parentRegion_volume
#print axioms p5_totalChildMultiplicityAt_lt_four_mul
#print axioms wholeIncidenceLift_of_labelledParentMass
#print axioms exists_twoStageRegularization

end Family8PaperFullCanonicalGroundingV522

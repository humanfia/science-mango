import Family8Grounding.Family8Prop66AFrostmanAspectGainAlgebraV1

/-!
# Union-volume floor to Proposition 6.6(A) average multiplicity

This file contains only the division-free algebra used after a large-`b`
union-volume estimate.  The analytic content remains entirely in two explicit
premises: a lower bound for the actual shaded union and the weakest product
budget comparing the actual shading mass with that lower bound.

In particular, no Equation (45) outer factor, inner factor, or large-`b`
analytic hypothesis is introduced here.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Prop66AFrostmanUnionVolumeAverageAdapterV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- The weakest product-form conversion from a certified union-volume floor
to an average-multiplicity bound.  It is valid without nonzero or finiteness
assumptions on the floor, the actual union volume, or the right-hand side. -/
theorem averageMultiplicity_le_of_shadingMass_le_rhs_mul_unionVolumeFloor
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota}
    (Y : Shading F) {unionVolumeFloor rhs : ENNReal}
    (hunion : unionVolumeFloor <= volume Y.shadedUnion)
    (hmass : Y.shadingMass <= rhs * unionVolumeFloor) :
    Y.averageMultiplicity <= rhs := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  exact hmass.trans (mul_le_mul' le_rfl hunion)

/-- Direct Equation (32) instance for an actual tube datum.  The scalar
`externalLoss` remains outside the Proposition 6.6(A) factor and is paid only
once.  The tube count is the literal cardinality of the datum's index type. -/
theorem actualTube_averageMultiplicity_le_loss_mul_proposition66AFrostmanFactor_of_unionVolumeFloor
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (a b : NNReal) (CF externalLoss unionVolumeFloor : ENNReal)
    (epsilon beta : Real)
    (hunion : unionVolumeFloor <= volume D.shading.shadedUnion)
    (hmass : D.shading.shadingMass <=
      (externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta) * unionVolumeFloor) :
    D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta := by
  exact averageMultiplicity_le_of_shadingMass_le_rhs_mul_unionVolumeFloor
    D.shading hunion hmass

#print axioms
  averageMultiplicity_le_of_shadingMass_le_rhs_mul_unionVolumeFloor
#print axioms
  actualTube_averageMultiplicity_le_loss_mul_proposition66AFrostmanFactor_of_unionVolumeFloor

end
end Family8Prop66AFrostmanUnionVolumeAverageAdapterV1

import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1

/-!
# Lemma 6.9 same-object density/cardinality payment

This file supplies only the two product inequalities needed around the
Lemma 6.9 union-volume floor for the shading of one actual tube datum.
The overlap factor is kept in the literal dyadic form
`levels.card * C * A`; no division or cancellation is performed.

The two scalar premises are exactly the remaining lower- and upper-volume
budgets after using the existing actual tube-volume sandwich.  In particular,
this file does not assert a pair-overlap estimate or an average-multiplicity
bound.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8Lemma69ActualTubeDensityCardPaymentV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8ActualFamilyVolumePackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- The exact same-object scalar payment around the Lemma 6.9 union floor.

The first conclusion is the absorption premise for the dyadic overlap
producer with `Q = levels.card * C * A`.  The second is precisely the mass
premise consumed by the union-floor-to-average adapter.  The hypotheses
`habsorbScalar` and `hupperScalar` are left in cross-multiplied form. -/
theorem lemma69_actualTube_productPayments_of_densityCardBudgets
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {levelIndex : Type*}
    (D : ActualTubeDatum delta index)
    (levels : Finset levelIndex)
    (densityFloor C A L rhs : ENNReal)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdensity : densityFloor <= D.shading.shadingDensity)
    (habsorbScalar :
      L * (((levels.card : ENNReal) * C * A)) <=
        densityFloor *
          ((Fintype.card index : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)))
    (hupperScalar :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) <=
        rhs * L) :
    L * (((levels.card : ENNReal) * C * A)) <=
        D.shading.shadingMass ∧
      D.shading.shadingMass <= rhs * L := by
  constructor
  · calc
      L * (((levels.card : ENNReal) * C * A)) <=
          densityFloor *
            ((Fintype.card index : ENNReal) *
              ((delta : ENNReal) ^ 2 / 2)) := habsorbScalar
      _ <= D.shading.shadingDensity * D.actualFamilyVolume := by
        exact mul_le_mul' hdensity
          (card_mul_half_sq_le_actualFamilyVolume D hdeltaHalf)
      _ = D.shading.shadingMass := by
        simpa only [ActualTubeDatum.actualFamilyVolume] using
          (shadingDensity_mul_familyVolume D.shading)
  · calc
      D.shading.shadingMass <= D.actualFamilyVolume := by
        simpa only [ActualTubeDatum.actualFamilyVolume] using
          D.shading.shadingMass_le_familyVolume
      _ <= (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) :=
        actualFamilyVolume_le_card_mul_eight_sq D hdeltaHalf
      _ <= rhs * L := hupperScalar

#print axioms lemma69_actualTube_productPayments_of_densityCardBudgets

end
end Family8Lemma69ActualTubeDensityCardPaymentV1

import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1
import Family8Grounding.Family8SameOccurrenceCarrierFloorCrossV1
import Mathlib.Tactic

/-!
# Local-card same-occurrence carrier-floor adapter

This file is the scalar adapter used after one occurrence, one surviving
fibre, and one side bucket have already been fixed.  The source-density
payment is weighted by the cardinality `m` of that surviving fibre, while
the clean bucket has at most `m` positive carriers.  Consequently `m`
cancels inside the carrier-floor argument and does not enter the loss.

No occurrence, side label, or bucket is selected here.  In particular, the
adapter has no global active-card or `R.card` input.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SameOccurrenceLocalCardCarrierFloorAdapterV1

open Submission.Kakeya.ConvexGeometry
open Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SameOccurrenceCarrierFloorCrossV1
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota]
variable {kappa : Type v} [Fintype kappa] [DecidableEq kappa]
variable {F : ConvexFamily iota} {G : ConvexFamily kappa}

/-- A surviving-fibre body-density payment and the retained mass of its
same-occurrence side bucket give a carrier-floor lower bound.  The clean
bucket index cardinality is compared only with the local surviving-fibre
cardinality `m`; `m` is eliminated and does not occur in the conclusion. -/
theorem localCard_sourceDensity_mul_area_le_quantitativeCarrierFloor
    (Z : Shading F) (Yclean : Shading G)
    {sourceDensity area m J occurrenceLoss bucketLoss : ENNReal}
    (hclean : Yclean.shadingMass ≠ 0)
    (hdensityPayment :
      sourceDensity * (m * area) <=
        occurrenceLoss * Z.shadingMass)
    (hbucketRetained :
      J * Z.shadingMass <= bucketLoss * Yclean.shadingMass)
    (hcleanCard : (Fintype.card kappa : ENNReal) <= m) :
    J * (sourceDensity * area) <=
      ((occurrenceLoss * bucketLoss) * 2) *
        quantitativeCarrierFloor Yclean := by
  have hretained :
      J * (occurrenceLoss * Z.shadingMass) <=
        (occurrenceLoss * bucketLoss) * Yclean.shadingMass := by
    calc
      J * (occurrenceLoss * Z.shadingMass) =
          occurrenceLoss * (J * Z.shadingMass) := by ac_rfl
      _ <= occurrenceLoss * (bucketLoss * Yclean.shadingMass) :=
        mul_le_mul' le_rfl hbucketRetained
      _ = (occurrenceLoss * bucketLoss) * Yclean.shadingMass := by
        ac_rfl
  have hcount :
      (Fintype.card kappa : ENNReal) * 2 <= 2 * m := by
    calc
      (Fintype.card kappa : ENNReal) * 2 <= m * 2 :=
        mul_le_mul' hcleanCard le_rfl
      _ = 2 * m := by ac_rfl
  exact
    sourceDensity_mul_area_le_sameObject_quantitativeCarrierFloor
      Yclean hclean hdensityPayment hretained hcount

/-- The local-card carrier-floor bound together with the literal
thresholded Cordoba cancellation.  The same Jacobian `J`, source density,
clean bucket, and local payment are used in both conclusions. -/
theorem localCard_sourceDensity_carrierFloorCross_and_thresholdedCordobaCancellation
    (Z : Shading F) (Yclean : Shading G)
    {sourceDensity m J occurrenceLoss bucketLoss KT : ENNReal}
    (rho r sideUpper : NNReal)
    (hclean : Yclean.shadingMass ≠ 0)
    (hdensityPayment :
      sourceDensity *
          (m * ((rho : ENNReal) ^ 2 / 2)) <=
        occurrenceLoss * Z.shadingMass)
    (hbucketRetained :
      J * Z.shadingMass <= bucketLoss * Yclean.shadingMass)
    (hcleanCard : (Fintype.card kappa : ENNReal) <= m) :
    J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2)) <=
        ((occurrenceLoss * bucketLoss) * 2) *
          quantitativeCarrierFloor Yclean /\
      (J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideUpper)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean))) <=
        ((occurrenceLoss * bucketLoss) * 2) *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            ((((sideUpper)⁻¹ * r : NNReal) : ENNReal) ^ 3))) := by
  have hfloor :=
    localCard_sourceDensity_mul_area_le_quantitativeCarrierFloor
      (Z := Z) (Yclean := Yclean)
      (sourceDensity := sourceDensity)
      (area := (rho : ENNReal) ^ 2 / 2)
      (m := m) (J := J)
      (occurrenceLoss := occurrenceLoss) (bucketLoss := bucketLoss)
      hclean hdensityPayment hbucketRetained hcleanCard
  have hcancel :=
    quantitativeCarrierFloorDensity_mul_thresholdedCordobaScale_le
      Yclean J sourceDensity ((occurrenceLoss * bucketLoss) * 2) KT
        rho r sideUpper hfloor
  exact ⟨hfloor, hcancel⟩

#print axioms localCard_sourceDensity_mul_area_le_quantitativeCarrierFloor
#print axioms
  localCard_sourceDensity_carrierFloorCross_and_thresholdedCordobaCancellation

end
end Family8SameOccurrenceLocalCardCarrierFloorAdapterV1

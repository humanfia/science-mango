import Family8Grounding.Family8QuantitativeCarrierPopularityRestrictionV3
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
import Mathlib.Tactic

/-!
# Same-occurrence carrier-floor cancellation

The same-occurrence carrier-floor producer supplies a multiplication-form
lower bound

`J * (sourceDensity * (rho ^ 2 / 2)) <= loss * floor`.

The Córdoba scale for the very same selected bucket contains
`angleScaleCap * (numerator / floor)`.  This file performs only the ensuing
`ENNReal` cancellation.  In particular, `J`, `sourceDensity`, and `rho`
remain visible, and no Frostman or DSO upper bound is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1

open Submission.Kakeya.ConvexGeometry
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6

noncomputable section

/-- Pure `ENNReal` cancellation of a positive finite carrier floor against
the literal denominator in a Córdoba scale. -/
theorem floorMultiplication_mul_cordobaScale_le
    (J sourceDensity rho loss KT angleScaleCap numerator floor : ENNReal)
    (hfloor0 : floor ≠ 0) (hfloorTop : floor ≠ ∞)
    (hfloor :
      J * (sourceDensity * (rho ^ 2 / 2)) <= loss * floor) :
    (J * (sourceDensity * (rho ^ 2 / 2))) *
        (KT * (angleScaleCap * (numerator / floor))) <=
      loss * (KT * (angleScaleCap * numerator)) := by
  have hcancel : floor * (numerator / floor) = numerator := by
    simpa only [mul_comm] using
      (ENNReal.div_mul_cancel hfloor0 hfloorTop :
        (numerator / floor) * floor = numerator)
  calc
    (J * (sourceDensity * (rho ^ 2 / 2))) *
        (KT * (angleScaleCap * (numerator / floor))) <=
      (loss * floor) *
        (KT * (angleScaleCap * (numerator / floor))) :=
          mul_le_mul' hfloor le_rfl
    _ = loss * (KT * (angleScaleCap *
        (floor * (numerator / floor)))) := by ac_rfl
    _ = loss * (KT * (angleScaleCap * numerator)) := by rw [hcancel]

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {F : ConvexFamily iota}

/-- The quantitative carrier floor has the positivity and finiteness needed
by the pure cancellation lemma.  Thus the multiplication-form conclusion of
the same-occurrence density producer is already sufficient: no additional
floor hypothesis is exposed to downstream consumers. -/
theorem quantitativeCarrierFloorDensity_mul_cordobaScale_le
    (Ybucket : Shading F)
    (J sourceDensity loss KT angleScaleCap numerator : ENNReal)
    (rho : NNReal)
    (hfloor :
      J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Ybucket) :
    (J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
        (KT * (angleScaleCap *
          (numerator / quantitativeCarrierFloor Ybucket))) <=
      loss * (KT * (angleScaleCap * numerator)) := by
  exact floorMultiplication_mul_cordobaScale_le
    J sourceDensity (rho : ENNReal) loss KT angleScaleCap numerator
      (quantitativeCarrierFloor Ybucket)
      (quantitativeCarrierFloor_ne_zero Ybucket)
      (quantitativeCarrierFloor_ne_top Ybucket) hfloor

/-- Literal specialization to the thresholded angle scale occurring in the
greedy-high same-occurrence Córdoba endpoint.  Taking `sideUpper` to be
`sideShapeUpper label 2` makes the premise definitionally identical to the
carrier-floor multiplication inequality returned for that selected bucket.
-/
theorem quantitativeCarrierFloorDensity_mul_thresholdedCordobaScale_le
    (Ybucket : Shading F)
    (J sourceDensity loss KT : ENNReal)
    (rho r sideUpper : NNReal)
    (hfloor :
      J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Ybucket) :
    (J * (sourceDensity * ((rho : ENNReal) ^ 2 / 2))) *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideUpper)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            quantitativeCarrierFloor Ybucket))) <=
      loss *
        (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          ((((sideUpper)⁻¹ * r : NNReal) : ENNReal) ^ 3))) := by
  exact quantitativeCarrierFloorDensity_mul_cordobaScale_le
    Ybucket J sourceDensity loss KT
      (certifiedPlankThresholdedAngleScaleCap 576)
      ((((sideUpper)⁻¹ * r : NNReal) : ENNReal) ^ 3) rho hfloor

#print axioms floorMultiplication_mul_cordobaScale_le
#print axioms quantitativeCarrierFloorDensity_mul_cordobaScale_le
#print axioms quantitativeCarrierFloorDensity_mul_thresholdedCordobaScale_le

end
end Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1

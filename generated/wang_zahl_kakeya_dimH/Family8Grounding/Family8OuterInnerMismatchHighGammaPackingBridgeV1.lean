import Family8Grounding.Family8EndpointIdentitySourceTauHighGammaInnerReserveV1
import Family8Grounding.Family8Prop66InnerScaleMismatchAbsorptionV1
import Mathlib.Tactic

/-!
# Absorbing the genuine outer/inner label mismatch into endpoint packing

The normalized outer winner and the selected inner parent have independent
John labels.  The existing two-floor theorem bounds their exact Proposition
6.6 inner-scale mismatch by

`(delta / 576)^(-beta) * (delta / 11943936)^(2*beta-2)`.

At the endpoint this is exactly a finite numerical constant times
`delta^(-(2-beta))`.  The latter power is already present in the automatic
endpoint packing coefficient.  This file performs that scalar cancellation
without identifying the two labels, and supplies the product consumer needed
by the loss-aware same-`q` DSO route.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8OuterInnerMismatchHighGammaPackingBridgeV1

open Family8EndpointIdentitySourceTauHighGammaInnerReserveV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8Prop66InnerScaleMismatchAbsorptionV1

noncomputable section

/-- The finite endpoint cost of using independent outer and inner John labels.
It contains no power of `delta`. -/
def outerInnerMismatchEndpointConstant (beta : Real) : ENNReal :=
  (576 : ENNReal) ^ beta *
    (11943936 : ENNReal) ^ (2 - 2 * beta)

/-- Exact extraction of the geometric endpoint power from the two honest
label floors. -/
theorem endpointFloorMismatchPower_eq_constant_mul_deltaPower
    {delta : NNReal} (hdelta : 0 < delta) (beta : Real) :
    (((delta / 576 : NNReal) : ENNReal) ^ (-beta)) *
        (((delta / 11943936 : NNReal) : ENNReal) ^ (2 * beta - 2)) =
      outerInnerMismatchEndpointConstant beta *
        (delta : ENNReal) ^ (-(2 - beta)) := by
  let D : ENNReal := delta
  have hD0 : D ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hDTop : D ≠ ∞ := ENNReal.coe_ne_top
  have hdiv (C : ENNReal) (hC0 : C ≠ 0) (t : Real) :
      (D / C) ^ t = D ^ t * C ^ (-t) := by
    rw [div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hDTop (ENNReal.inv_ne_top.mpr hC0) t,
      ENNReal.inv_rpow, <- ENNReal.rpow_neg]
  rw [ENNReal.coe_div (by norm_num : (576 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (11943936 : NNReal) ≠ 0)]
  change
    (D / (576 : ENNReal)) ^ (-beta) *
        (D / (11943936 : ENNReal)) ^ (2 * beta - 2) = _
  rw [hdiv 576 (by norm_num) (-beta),
    hdiv 11943936 (by norm_num) (2 * beta - 2)]
  unfold outerInnerMismatchEndpointConstant
  calc
    (D ^ (-beta) * (576 : ENNReal) ^ (-(-beta))) *
        (D ^ (2 * beta - 2) *
          (11943936 : ENNReal) ^ (-(2 * beta - 2))) =
      ((576 : ENNReal) ^ beta *
          (11943936 : ENNReal) ^ (2 - 2 * beta)) *
        (D ^ (-beta) * D ^ (2 * beta - 2)) := by
      rw [show -(-beta) = beta by ring,
        show -(2 * beta - 2) = 2 - 2 * beta by ring]
      ac_rfl
    _ = ((576 : ENNReal) ^ beta *
          (11943936 : ENNReal) ^ (2 - 2 * beta)) *
        D ^ (-(2 - beta)) := by
      rw [<- ENNReal.rpow_add (-beta) (2 * beta - 2) hD0 hDTop]
      congr 1
      ring

/-- The endpoint packing coefficient absorbs the complete geometric power
of the independent-label mismatch.  Only the finite numerical label cost is
left outside. -/
theorem endpointFloorMismatchPower_le_constant_mul_endpointPacking
    {delta : NNReal} (hdelta : 0 < delta)
    {beta : Real} (hbetaTwo : beta <= 2) :
    (((delta / 576 : NNReal) : ENNReal) ^ (-beta)) *
        (((delta / 11943936 : NNReal) : ENNReal) ^ (2 * beta - 2)) <=
      outerInnerMismatchEndpointConstant beta *
        (endpointIdentitySourceTauPackingKatzTaoConstant delta delta) ^
          (1 - beta / 2) := by
  rw [endpointFloorMismatchPower_eq_constant_mul_deltaPower hdelta beta]
  exact mul_le_mul' le_rfl
    (delta_negative_two_sub_gamma_le_endpointPacking_one_sub_gamma_half
      (delta := delta) hdelta hbetaTwo)

/-- Payload-independent seam.  Any geometric producer which bounds the true
outer/inner mismatch by the two endpoint floors may feed this theorem; no
identity or comparison between the labels is required. -/
theorem mismatch_le_constant_mul_endpointPacking_of_endpointFloorBound
    {delta : NNReal} {mismatch : ENNReal} (hdelta : 0 < delta)
    {beta : Real} (hbetaTwo : beta <= 2)
    (hmismatch : mismatch <=
      (((delta / 576 : NNReal) : ENNReal) ^ (-beta)) *
        (((delta / 11943936 : NNReal) : ENNReal) ^ (2 * beta - 2))) :
    mismatch <= outerInnerMismatchEndpointConstant beta *
      (endpointIdentitySourceTauPackingKatzTaoConstant delta delta) ^
        (1 - beta / 2) :=
  hmismatch.trans
    (endpointFloorMismatchPower_le_constant_mul_endpointPacking
      hdelta hbetaTwo)

/-- Generic coefficient absorption.  A factor bounded by
`loss * packing^(1-beta/2)` can be folded into the Frostman coefficient
`packing * CF`; the external loss stays linear. -/
theorem mismatch_mul_frostmanFactor_le_loss_mul_packedFrostmanFactor
    {delta a b : NNReal} {tubeCount : Nat}
    {CF packing mismatch loss : ENNReal} {epsilon beta : Real}
    (hbetaTwo : beta <= 2)
    (hmismatch : mismatch <= loss * packing ^ (1 - beta / 2)) :
    mismatch *
        proposition66AFrostmanFactor delta a b tubeCount CF epsilon beta <=
      loss * proposition66AFrostmanFactor delta a b tubeCount
        (packing * CF) epsilon beta := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  unfold proposition66AFrostmanFactor
  rw [ENNReal.mul_rpow_of_nonneg packing CF hp]
  calc
    mismatch *
        ((delta : ENNReal) ^ (-epsilon) * CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta tubeCount ^
            (1 - beta / 2)) =
      (mismatch * CF ^ (1 - beta / 2)) *
        ((delta : ENNReal) ^ (-epsilon) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta tubeCount ^
            (1 - beta / 2)) := by ac_rfl
    _ <= ((loss * packing ^ (1 - beta / 2)) *
          CF ^ (1 - beta / 2)) *
        ((delta : ENNReal) ^ (-epsilon) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta tubeCount ^
            (1 - beta / 2)) :=
      mul_le_mul' (mul_le_mul' hmismatch le_rfl) le_rfl
    _ = loss *
        ((delta : ENNReal) ^ (-epsilon) *
          (packing ^ (1 - beta / 2) * CF ^ (1 - beta / 2)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2) *
          (delta : ENNReal) ^ (-2 * beta) *
          proposition66ACardScaleVolume delta tubeCount ^
            (1 - beta / 2)) := by ac_rfl

/-- Product consumer for two genuine, independent labels.  The mismatch is
paid by the endpoint packing coefficient, while the existing approximate
product-count loss is retained exactly once. -/
theorem outer_mul_inner_le_mismatchLoss_countLoss_mul_packedFrostmanFactor
    {delta outerA outerB innerA innerB : NNReal}
    {plankCount tubesPerPlank totalCount : Nat}
    {CF packing countLoss numericalLoss : ENNReal}
    {epsilon beta : Real}
    (hdelta : 0 < delta)
    (houterA : 0 < outerA) (houterB : 0 < outerB)
    (hinnerA : 0 < innerA) (hinnerB : 0 < innerB)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcount : ((plankCount * tubesPerPlank : Nat) : ENNReal) <=
      countLoss * (totalCount : ENNReal))
    (hmismatch :
      prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta <=
        numericalLoss * packing ^ (1 - beta / 2)) :
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank
          epsilon beta <=
      (numericalLoss * countLoss ^ (1 - beta / 2)) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          (packing * CF) epsilon beta := by
  have hproduct :=
    proposition66AOuterFactor_mul_innerFactor_le_innerScaleMismatch_countLoss_mul_frostmanFactor
      (CF := CF) (countLoss := countLoss) (epsilon := epsilon) (beta := beta)
      hdelta houterA houterB hinnerA hinnerB hbeta hbetaOne hcount
  have habsorb :=
    mismatch_mul_frostmanFactor_le_loss_mul_packedFrostmanFactor
      (delta := delta) (a := outerA) (b := outerB)
      (tubeCount := totalCount) (CF := CF) (packing := packing)
      (mismatch := prop66InnerScaleMismatchLoss
        outerA outerB innerA innerB beta)
      (loss := numericalLoss) (epsilon := epsilon) (beta := beta)
      (hbetaOne.trans (by norm_num)) hmismatch
  calc
    proposition66AOuterFactor delta outerA outerB plankCount CF epsilon beta *
        proposition66AInnerFactor delta innerA innerB tubesPerPlank
          epsilon beta <=
      (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
        countLoss ^ (1 - beta / 2)) *
          proposition66AFrostmanFactor delta outerA outerB totalCount
            CF epsilon beta := hproduct
    _ = countLoss ^ (1 - beta / 2) *
        (prop66InnerScaleMismatchLoss outerA outerB innerA innerB beta *
          proposition66AFrostmanFactor delta outerA outerB totalCount
            CF epsilon beta) := by ac_rfl
    _ <= countLoss ^ (1 - beta / 2) *
        (numericalLoss *
          proposition66AFrostmanFactor delta outerA outerB totalCount
            (packing * CF) epsilon beta) := mul_le_mul' le_rfl habsorb
    _ = (numericalLoss * countLoss ^ (1 - beta / 2)) *
        proposition66AFrostmanFactor delta outerA outerB totalCount
          (packing * CF) epsilon beta := by ac_rfl

#print axioms endpointFloorMismatchPower_eq_constant_mul_deltaPower
#print axioms endpointFloorMismatchPower_le_constant_mul_endpointPacking
#print axioms mismatch_le_constant_mul_endpointPacking_of_endpointFloorBound
#print axioms mismatch_mul_frostmanFactor_le_loss_mul_packedFrostmanFactor
#print axioms outer_mul_inner_le_mismatchLoss_countLoss_mul_packedFrostmanFactor

end
end Family8OuterInnerMismatchHighGammaPackingBridgeV1

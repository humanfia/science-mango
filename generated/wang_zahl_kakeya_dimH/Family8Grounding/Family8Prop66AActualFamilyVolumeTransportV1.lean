import Family8Grounding.Family8Prop66AFrostmanAspectGainAlgebraV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

/-!
# Proposition 6.6(A): card-scale volume to actual tube volume

The paper writes `delta^2 * #T`, while the Family 8 Frostman endpoint keeps
the genuine sum of tube volumes.  These quantities are comparable, not equal.
This file transports between them using the literal tube-volume constants
`1 / 2` and `8`.
-/

open scoped ENNReal NNReal BigOperators
open MeasureTheory

namespace Family8Prop66AActualFamilyVolumeTransportV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ActualFamilyVolumePackingV1
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8Prop66AFrostmanAspectGainAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- The paper's `delta^2 * #T` is at most twice the actual summed volume.
This is the summed lower tube-volume estimate, with no nonempty-index
assumption and no equality claim. -/
theorem proposition66ACardScaleVolume_le_two_mul_actualFamilyVolume
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    proposition66ACardScaleVolume delta (Fintype.card iota) ≤
      2 * D.actualFamilyVolume := by
  have hlower :
      (Fintype.card iota : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) ≤ D.actualFamilyVolume := by
    unfold ActualTubeDatum.actualFamilyVolume familyVolume
    simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
    calc
      (Fintype.card iota : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i : iota, (delta : ENNReal) ^ 2 / 2 := by simp
      _ ≤ ∑ i : iota, volume (D.family.tubes i).carrier := by
        exact Finset.sum_le_sum fun i _ =>
          (D.family.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
  calc
    proposition66ACardScaleVolume delta (Fintype.card iota) =
        2 * ((Fintype.card iota : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) := by
      unfold proposition66ACardScaleVolume
      rw [div_eq_mul_inv]
      have htwo : (2 : ENNReal)⁻¹ * 2 = 1 :=
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      calc
        (delta : ENNReal) ^ 2 * (Fintype.card iota : ENNReal) =
            ((delta : ENNReal) ^ 2 * (Fintype.card iota : ENNReal)) * 1 := by
          rw [mul_one]
        _ = ((delta : ENNReal) ^ 2 * (Fintype.card iota : ENNReal)) *
            ((2 : ENNReal)⁻¹ * 2) := by rw [htwo]
        _ = 2 * ((Fintype.card iota : ENNReal) *
            ((delta : ENNReal) ^ 2 * (2 : ENNReal)⁻¹)) := by
          ac_rfl
    _ ≤ 2 * D.actualFamilyVolume := mul_le_mul_right hlower 2

/-- Conversely, the actual summed volume is at most eight times the paper's
card-scale volume. -/
theorem actualFamilyVolume_le_eight_mul_proposition66ACardScaleVolume
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    D.actualFamilyVolume ≤
      8 * proposition66ACardScaleVolume delta (Fintype.card iota) := by
  calc
    D.actualFamilyVolume ≤
        (Fintype.card iota : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) :=
      actualFamilyVolume_le_card_mul_eight_sq D hdeltaHalf
    _ = 8 * proposition66ACardScaleVolume delta (Fintype.card iota) := by
      unfold proposition66ACardScaleVolume
      ac_rfl

/-- For `beta ≤ 2`, the paper's card-scale Frostman RHS is bounded by the
actual-volume RHS with the explicit lower-volume comparison cost `2^(1-beta/2)`.
-/
theorem frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {epsilon beta : Real}
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) (hbetaTwo : beta ≤ 2) :
    frostmanMultiplicityRHS delta
        (proposition66ACardScaleVolume delta (Fintype.card iota))
        epsilon beta ≤
      frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta *
        (2 : ENNReal) ^ (1 - beta / 2) :=
  frostmanMultiplicityRHS_le_of_volume_le_factor_mul hbetaTwo
    (proposition66ACardScaleVolume_le_two_mul_actualFamilyVolume
      D hdeltaHalf)

/-- The reverse RHS transport uses the explicit upper tube-volume comparison
cost `8^(1-beta/2)`. -/
theorem frostmanMultiplicityRHS_actual_le_cardScale_mul_eight_rpow
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {epsilon beta : Real}
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) (hbetaTwo : beta ≤ 2) :
    frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta ≤
      frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta (Fintype.card iota))
          epsilon beta *
        (8 : ENNReal) ^ (1 - beta / 2) :=
  frostmanMultiplicityRHS_le_of_volume_le_factor_mul hbetaTwo
    (actualFamilyVolume_le_eight_mul_proposition66ACardScaleVolume
      D hdeltaHalf)

/-- Honest connector from the exact paper scalar to the actual-volume Family 8
normalization.  The only loss is the proved tube-volume constant two; no
multiplicity estimate is assumed or produced here. -/
theorem proposition66AFrostmanFactor_le_actualRHS_with_two_rpow
    {delta a b : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    {CF : ENNReal} {epsilon beta : Real}
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) (hbetaTwo : beta ≤ 2) :
    proposition66AFrostmanFactor delta a b (Fintype.card iota)
        CF epsilon beta ≤
      (proposition66AFrostmanAspectGain a b CF beta *
        (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta := by
  rw [proposition66AFrostmanFactor_eq_gain_mul_frostmanMultiplicityRHS]
  have hRHS :=
    frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
      (epsilon := epsilon) (beta := beta) D hdeltaHalf hbetaTwo
  calc
    proposition66AFrostmanAspectGain a b CF beta *
        frostmanMultiplicityRHS delta
          (proposition66ACardScaleVolume delta (Fintype.card iota))
          epsilon beta ≤
      proposition66AFrostmanAspectGain a b CF beta *
        (frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta *
          (2 : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul_right hRHS _
    _ = (proposition66AFrostmanAspectGain a b CF beta *
          (2 : ENNReal) ^ (1 - beta / 2)) *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta := by
      ac_rfl

#print axioms proposition66ACardScaleVolume_le_two_mul_actualFamilyVolume
#print axioms actualFamilyVolume_le_eight_mul_proposition66ACardScaleVolume
#print axioms frostmanMultiplicityRHS_cardScale_le_actual_mul_two_rpow
#print axioms frostmanMultiplicityRHS_actual_le_cardScale_mul_eight_rpow
#print axioms proposition66AFrostmanFactor_le_actualRHS_with_two_rpow

end

end Family8Prop66AActualFamilyVolumeTransportV1

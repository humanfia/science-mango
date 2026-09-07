import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open scoped ENNReal NNReal BigOperators
open MeasureTheory

namespace Family8ActualFamilyVolumePackingV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# From actual tube packing to summed family volume

This file keeps the geometric packing input in cardinality form and performs
the exact conversion to the summed-volume normalization used by `K_F`.
-/

/-- Summing the uniform actual tube-volume upper bound over an arbitrary
indexed tube family. -/
theorem actualFamilyVolume_le_card_mul_eight_sq
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    D.actualFamilyVolume <=
      (Fintype.card iota : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (∑ i : iota, volume (D.family.tubes i).carrier) <=
        ∑ _i : iota, 8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        (D.family.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (Fintype.card iota : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by simp

/-- A `C delta^(-4)` packing bound becomes the exact
`8 C delta^(-2)` summed-volume bound needed in the all-Frostman branch. -/
theorem actualFamilyVolume_le_of_card_rpow_neg_four
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) {C : ENNReal}
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hcard :
      (Fintype.card iota : ENNReal) <=
        C * (delta : ENNReal) ^ (-4 : Real)) :
    D.actualFamilyVolume <=
      (8 * C) * (delta : ENNReal) ^ (-2 : Real) := by
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    D.actualFamilyVolume <=
        (Fintype.card iota : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) :=
      actualFamilyVolume_le_card_mul_eight_sq D hdeltaHalf
    _ <= (C * (delta : ENNReal) ^ (-4 : Real)) *
          (8 * (delta : ENNReal) ^ 2) := by gcongr
    _ = (8 * C) *
          ((delta : ENNReal) ^ (-4 : Real) *
            (delta : ENNReal) ^ 2) := by ac_rfl
    _ = (8 * C) *
          ((delta : ENNReal) ^ (-4 : Real) *
            (delta : ENNReal) ^ (2 : Real)) :=
      congrArg (fun y =>
        (8 * C) * ((delta : ENNReal) ^ (-4 : Real) * y))
        (ENNReal.rpow_natCast (delta : ENNReal) 2).symm
    _ = (8 * C) *
          (delta : ENNReal) ^ ((-4 : Real) + 2) := by
      rw [ENNReal.rpow_add (-4 : Real) 2 hd0 hdTop]
    _ = (8 * C) * (delta : ENNReal) ^ (-2 : Real) := by norm_num

#print axioms actualFamilyVolume_le_card_mul_eight_sq
#print axioms actualFamilyVolume_le_of_card_rpow_neg_four

end

end Family8ActualFamilyVolumePackingV1

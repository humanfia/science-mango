import Family8Grounding.Family8CommonPointTubePackingV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Family8Grounding.Family8StickyParentPopularCanonicalUnionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickySourceCardFallbackV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8CommonPointTubePackingV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyParentPopularCanonicalUnionV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A quantitative source-card fallback for the Sticky popular factor

The pointwise common-point packing theorem bounds the summed volume by
C delta^-2.  The lower volume of every actual tube then gives the honest
but coarse source-card estimate 2 C delta^-4.  Cubing this estimate and using
the automatic parent-hull volume bound isolates the current unavoidable
loss delta^-12.  This is not claimed to be the final small-loss argument.
-/

/-- Admissible tubes in the unit ball obey the coarse global delta^-4
cardinality estimate obtained from the proved pointwise packing theorem. -/
theorem actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (Fintype.card iota : ENNReal) ≤
      (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hcard :=
    indexCard_le_two_mul_delta_rpow_neg_two_mul_actualFamilyVolume
      D hD.delta_pos hD.delta_le_half
  have hvolume := actualFamilyVolume_le_commonPointPacking
    D hD hdeltaSmall
  calc
    (Fintype.card iota : ENNReal) ≤
        2 * (delta : ENNReal) ^ (-2 : Real) * D.actualFamilyVolume :=
      hcard
    _ ≤ 2 * (delta : ENNReal) ^ (-2 : Real) *
        (commonPointFamilyVolumeConstant *
          (delta : ENNReal) ^ (-2 : Real)) := by gcongr
    _ = (2 * commonPointFamilyVolumeConstant) *
        ((delta : ENNReal) ^ (-2 : Real) *
          (delta : ENNReal) ^ (-2 : Real)) := by ac_rfl
    _ = (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ ((-2 : Real) + (-2 : Real)) := by
      rw [ENNReal.rpow_add (-2 : Real) (-2 : Real) hd0 hdTop]
    _ = (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by norm_num

/-- Cubing the coarse card estimate costs exactly delta^-12. -/
theorem actualTubeDatum_indexCard_cube_le_commonPointConstant_rpow_neg_twelve
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (Fintype.card iota : ENNReal) ^ 3 ≤
      (2 * commonPointFamilyVolumeConstant) ^ 3 *
        (delta : ENNReal) ^ (-12 : Real) := by
  have hcard :=
    actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
      D hD hdeltaSmall
  calc
    (Fintype.card iota : ENNReal) ^ 3 ≤
        ((2 * commonPointFamilyVolumeConstant) *
          (delta : ENNReal) ^ (-4 : Real)) ^ 3 := by gcongr
    _ = (2 * commonPointFamilyVolumeConstant) ^ 3 *
        ((delta : ENNReal) ^ (-4 : Real)) ^ 3 := by rw [mul_pow]
    _ = (2 * commonPointFamilyVolumeConstant) ^ 3 *
        (delta : ENNReal) ^ (-12 : Real) := by
      rw [← ENNReal.rpow_natCast ((delta : ENNReal) ^ (-4 : Real)) 3]
      rw [← ENNReal.rpow_mul]
      norm_num

/-- After the automatic hull bound, the literal popular factor is bounded by
a finite constant times the Katz--Tao error and delta^-12. -/
theorem stickyPopularCardCubeFactor_le_commonPointFallback
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho ≤ 1)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (katzTaoError : ENNReal) :
    stickyPopularCardCubeFactor S katzTaoError ≤
      (2048 * (2 * commonPointFamilyVolumeConstant) ^ 3) *
        katzTaoError * (delta : ENNReal) ^ (-12 : Real) := by
  have hcard :=
    actualTubeDatum_indexCard_cube_le_commonPointConstant_rpow_neg_twelve
      D hD hdeltaSmall
  have hhull :=
    volume_fullFamilyHullContainer_activeCoarseFamily_le_512
      D hD S hrhoOne
  unfold stickyPopularCardCubeFactor
  calc
    (Fintype.card iota : ENNReal) ^ 2 *
        (4 * (Fintype.card iota : ENNReal) * katzTaoError *
          volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space)) =
      4 * (Fintype.card iota : ENNReal) ^ 3 * katzTaoError *
        volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space) := by
      ring
    _ ≤ 4 *
        ((2 * commonPointFamilyVolumeConstant) ^ 3 *
          (delta : ENNReal) ^ (-12 : Real)) * katzTaoError * 512 := by
      gcongr
    _ = (2048 * (2 * commonPointFamilyVolumeConstant) ^ 3) *
        katzTaoError * (delta : ENNReal) ^ (-12 : Real) := by
      ring

/-- The fallback coefficient is finite; the remaining obstruction is its
fixed delta^-12 power together with the supplied Katz--Tao loss. -/
theorem commonPointStickyPopularFallbackConstant_ne_top :
    (2048 * (2 * commonPointFamilyVolumeConstant) ^ 3 : ENNReal) ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · norm_num
  · apply ENNReal.pow_ne_top
    apply ENNReal.mul_ne_top
    · norm_num
    · exact commonPointFamilyVolumeConstant_ne_top

#print axioms actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
#print axioms actualTubeDatum_indexCard_cube_le_commonPointConstant_rpow_neg_twelve
#print axioms stickyPopularCardCubeFactor_le_commonPointFallback
#print axioms commonPointStickyPopularFallbackConstant_ne_top

end
end Family8StickySourceCardFallbackV1

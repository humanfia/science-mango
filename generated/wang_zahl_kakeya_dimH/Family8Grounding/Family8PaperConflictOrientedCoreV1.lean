import Family8Grounding.Family8PaperConflictAnisotropicBoundsV4
import FamilyStickyGrounding.FamilyStickySameRadiusTubeContainmentCompatibleV1
import FamilyStickyRandomFiniteFloorParameterNetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictOrientedCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8CommonPointTubePackingV1
open Family8PaperConflictDirectionCoherenceV1
open Family8PaperConflictAnisotropicBoundsV4
open FamilyStickySameRadiusTubeContainmentCompatibleV1
open FamilyStickyTubeParentDirectionCoherenceV1

noncomputable section

/-! Deterministic projective orientation and its fixed normalized box. -/

def paperConflictOrientedTube {delta : NNReal}
    (anchor U : Tube delta) : Tube delta :=
  if ‖U.axis.direction - anchor.axis.direction‖ ≤ 8 * (delta : Real) then
    U
  else
    reversedTube U

@[simp]
theorem paperConflictOrientedTube_carrier
    {delta : NNReal} (anchor U : Tube delta) :
    (paperConflictOrientedTube anchor U).carrier = U.carrier := by
  rw [paperConflictOrientedTube]
  split_ifs
  · rfl
  · exact reversedTubeCarrier U

@[simp]
theorem paperConflictOrientedTube_midpoint
    {delta : NNReal} (anchor U : Tube delta) :
    tubeAxisMidpoint (paperConflictOrientedTube anchor U) =
      tubeAxisMidpoint U := by
  rw [paperConflictOrientedTube]
  split_ifs
  · rfl
  · simp only [tubeAxisMidpoint, reversedTube, reversedUnitSegmentBase,
      reversedUnitSegmentDirection, UnitSegment.endpoint]
    module

@[simp]
theorem paperConflictOrientedTube_center
    {delta : NNReal} (anchor U : Tube delta) :
    tubeCenter (paperConflictOrientedTube anchor U) = tubeCenter U := by
  change tubeAxisMidpoint (paperConflictOrientedTube anchor U) =
    tubeAxisMidpoint U
  exact paperConflictOrientedTube_midpoint anchor U

@[simp]
theorem paperConflictOrientedTube_twoFold
    {delta : NNReal} (anchor U : Tube delta) :
    twoFoldTubeCarrier (paperConflictOrientedTube anchor U) =
      twoFoldTubeCarrier U := by
  simp only [twoFoldTubeCarrier, paperConflictOrientedTube_center,
    paperConflictOrientedTube_carrier]

theorem essentiallyDistinct_oriented_iff
    {delta : NNReal} (anchor T U : Tube delta) :
    EssentiallyDistinct (paperConflictOrientedTube anchor T)
        (paperConflictOrientedTube anchor U) ↔
      EssentiallyDistinct T U := by
  simp only [EssentiallyDistinct, paperConflictOrientedTube_carrier]

theorem paperConflict_oriented_right
    {delta : NNReal} {anchor U : Tube delta}
    (hconflict : PaperConflict anchor U) :
    PaperConflict anchor (paperConflictOrientedTube anchor U) := by
  simpa only [PaperConflict, paperConflictOrientedTube_carrier,
    paperConflictOrientedTube_twoFold] using hconflict

theorem norm_orientedDirection_sub_anchor_le_eight_mul
    {delta : NNReal} {anchor U : Tube delta}
    (hconflict : PaperConflict anchor U) :
    ‖(paperConflictOrientedTube anchor U).axis.direction -
        anchor.axis.direction‖ ≤ 8 * (delta : Real) := by
  have hprojective :=
    unorientedDirectionClose_eight_mul_of_paperConflict hconflict
  rw [paperConflictOrientedTube]
  split_ifs with hforward
  · rcases hprojective with hprojective | hprojective
    · simpa only [norm_sub_rev] using hprojective
    · exact hforward
  · rcases hprojective with hprojective | hprojective
    · exact (hforward (by simpa only [norm_sub_rev] using hprojective)).elim
    · change ‖(-U.axis.direction) - anchor.axis.direction‖ ≤ _
      have heq :
          (-U.axis.direction) - anchor.axis.direction =
            -(U.axis.direction + anchor.axis.direction) := by module
      rw [heq, norm_neg]
      simpa only [add_comm] using hprojective

def paperConflictConstantMesh : Real := (1 : Real) / 10000

def paperConflictNormalizedCoordinates {delta : NNReal}
    (anchor U : Tube delta) : Fin 7 → Real :=
  let V := paperConflictOrientedTube anchor U
  ![tubePointLongitudinal (tubeAxisMidpoint anchor) V,
    tubePointTransverse (tubeAxisMidpoint anchor) V 0 / (delta : Real),
    tubePointTransverse (tubeAxisMidpoint anchor) V 1 / (delta : Real),
    tubePointTransverse (tubeAxisMidpoint anchor) V 2 / (delta : Real),
    (V.axis.direction - anchor.axis.direction) 0 / (delta : Real),
    (V.axis.direction - anchor.axis.direction) 1 / (delta : Real),
    (V.axis.direction - anchor.axis.direction) 2 / (delta : Real)]

theorem abs_paperConflictNormalizedCoordinates_le_forty
    {delta : NNReal} (hdeltaPos : 0 < delta)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    {anchor U : Tube delta} (hconflict : PaperConflict anchor U)
    (k : Fin 7) :
    |paperConflictNormalizedCoordinates anchor U k| ≤ 40 := by
  let V := paperConflictOrientedTube anchor U
  have hconflictV : PaperConflict anchor V := by
    simpa only [V] using paperConflict_oriented_right hconflict
  have hlong :
      |tubePointLongitudinal (tubeAxisMidpoint anchor) V| ≤ 2 :=
    abs_tubePointLongitudinal_anchor_le_two hdeltaSmall hconflictV
  have htrans :
      ‖tubePointTransverse (tubeAxisMidpoint anchor) V‖ ≤
        36 * (delta : Real) :=
    norm_tubePointTransverse_anchor_le_thirtySix_mul hdeltaSmall hconflictV
  have hdir :
      ‖V.axis.direction - anchor.axis.direction‖ ≤ 8 * (delta : Real) := by
    simpa only [V] using
      norm_orientedDirection_sub_anchor_le_eight_mul hconflict
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  fin_cases k
  · change |tubePointLongitudinal (tubeAxisMidpoint anchor) V| ≤ 40
    exact hlong.trans (by norm_num)
  all_goals
    change |_ / (delta : Real)| ≤ 40
    rw [abs_div, abs_of_pos hdeltaReal]
    apply (div_le_iff₀ hdeltaReal).2
  · exact (abs_apply_le_norm
      (tubePointTransverse (tubeAxisMidpoint anchor) V) 0).trans
        (htrans.trans (by nlinarith [hdeltaReal.le]))
  · exact (abs_apply_le_norm
      (tubePointTransverse (tubeAxisMidpoint anchor) V) 1).trans
        (htrans.trans (by nlinarith [hdeltaReal.le]))
  · exact (abs_apply_le_norm
      (tubePointTransverse (tubeAxisMidpoint anchor) V) 2).trans
        (htrans.trans (by nlinarith [hdeltaReal.le]))
  · exact (abs_apply_le_norm (V.axis.direction - anchor.axis.direction) 0).trans
      (hdir.trans (by nlinarith [hdeltaReal.le]))
  · exact (abs_apply_le_norm (V.axis.direction - anchor.axis.direction) 1).trans
      (hdir.trans (by nlinarith [hdeltaReal.le]))
  · exact (abs_apply_le_norm (V.axis.direction - anchor.axis.direction) 2).trans
      (hdir.trans (by nlinarith [hdeltaReal.le]))

#print axioms paperConflictOrientedTube_carrier
#print axioms paperConflictOrientedTube_twoFold
#print axioms paperConflict_oriented_right
#print axioms norm_orientedDirection_sub_anchor_le_eight_mul
#print axioms abs_paperConflictNormalizedCoordinates_le_forty

end

end Family8PaperConflictOrientedCoreV1

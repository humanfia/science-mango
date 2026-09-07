import Family8Grounding.Family8PaperConflictOrientedCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictOrientedCoordinatesV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CommonPointTubePackingV1
open Family8PaperConflictOrientedCoreV1

noncomputable section

theorem wide_anisotropic_close_of_floorCode_eq
    {delta : NNReal} (hdeltaPos : 0 < delta) (anchor T U : Tube delta)
    (hcode :
      FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
          paperConflictConstantMesh
          (paperConflictNormalizedCoordinates anchor) T =
        FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
          paperConflictConstantMesh
          (paperConflictNormalizedCoordinates anchor) U) :
    |tubePointLongitudinal (tubeAxisMidpoint anchor)
          (paperConflictOrientedTube anchor T) -
        tubePointLongitudinal (tubeAxisMidpoint anchor)
          (paperConflictOrientedTube anchor U)| ≤ (1 : Real) / 400 ∧
      dist
          (tubePointTransverse (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor T))
          (tubePointTransverse (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor U)) ≤ (delta : Real) / 100 ∧
      dist (paperConflictOrientedTube anchor T).axis.direction
          (paperConflictOrientedTube anchor U).axis.direction ≤
        (delta : Real) / 1000 := by
  have hmesh : 0 < paperConflictConstantMesh := by
    norm_num [paperConflictConstantMesh]
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have hfloor (k : Fin 7) :=
    FamilyStickyRandomFiniteFloorParameterNetV1.abs_coord_sub_lt_of_floorCode_eq
      hmesh (paperConflictNormalizedCoordinates anchor) hcode k
  have hphysical {a b : Real}
      (h : |a / (delta : Real) - b / (delta : Real)| <
        paperConflictConstantMesh) :
      |a - b| < (delta : Real) / 10000 := by
    rw [← sub_div, abs_div, abs_of_pos hdeltaReal,
      paperConflictConstantMesh] at h
    have h' := (div_lt_iff₀ hdeltaReal).mp h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h'
  have hlongStrict :
      |tubePointLongitudinal (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor T) -
          tubePointLongitudinal (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor U)| < (1 : Real) / 10000 := by
    simpa [paperConflictNormalizedCoordinates,
      paperConflictConstantMesh] using hfloor (0 : Fin 7)
  have htransCoord : ∀ j : Fin 3,
      |tubePointTransverse (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor T) j -
          tubePointTransverse (tubeAxisMidpoint anchor)
            (paperConflictOrientedTube anchor U) j| <
        (delta : Real) / 10000 := by
    intro j
    fin_cases j
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (1 : Fin 7))
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (2 : Fin 7))
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (3 : Fin 7))
  have hdirCoord : ∀ j : Fin 3,
      |((paperConflictOrientedTube anchor T).axis.direction -
            anchor.axis.direction) j -
          ((paperConflictOrientedTube anchor U).axis.direction -
            anchor.axis.direction) j| < (delta : Real) / 10000 := by
    intro j
    fin_cases j
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (4 : Fin 7))
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (5 : Fin 7))
    · exact hphysical (by
        simpa [paperConflictNormalizedCoordinates] using hfloor (6 : Fin 7))
  refine ⟨hlongStrict.le.trans (by norm_num), ?_, ?_⟩
  · apply dist_le_delta_div_hundred_of_coordinate_close
    intro j
    exact (htransCoord j).trans (by nlinarith [hdeltaReal])
  · have hclose :
        dist (paperConflictOrientedTube anchor T).axis.direction
            (paperConflictOrientedTube anchor U).axis.direction ≤
          (((delta / 10 : NNReal) : Real)) / 100 := by
      apply dist_le_delta_div_hundred_of_coordinate_close
      intro j
      have hj :
          |(paperConflictOrientedTube anchor T).axis.direction j -
              (paperConflictOrientedTube anchor U).axis.direction j| <
            (delta : Real) / 10000 := by
        have hj' := hdirCoord j
        simp only [PiLp.sub_apply] at hj'
        convert hj' using 1
        congr 1
        ring
      have hcoe :
          (((delta / 10 : NNReal) : Real)) / 1000 =
            (delta : Real) / 10000 := by
        rw [NNReal.coe_div]
        norm_num
        ring
      rwa [hcoe]
    have hcoe :
        (((delta / 10 : NNReal) : Real)) / 100 =
          (delta : Real) / 1000 := by
      rw [NNReal.coe_div]
      norm_num
      ring
    rwa [hcoe] at hclose

#print axioms wide_anisotropic_close_of_floorCode_eq

end

end Family8PaperConflictOrientedCoordinatesV5

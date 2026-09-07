import Family8Grounding.Family8PaperConflictOwnerParentFrameFiniteCodeV8
import FamilyStickyGrounding.FamilyStickySameRadiusTubeContainmentCompatibleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictOwnerParentFramePhysicalBridgeV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CommonPointTubePackingV1
open Family8PaperConflictOwnerParentFrameBoundsV2
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open FamilyStickySameRadiusTubeContainmentCompatibleV1

noncomputable section

/-!
# Physical geometry of one parent-frame code cell

The split finite code gives componentwise estimates.  This file turns them
into Euclidean transverse, direction, midpoint, and corresponding-axis-point
bounds.  It then gives a literal `5*rho` tube containing every owner in the
same code as a chosen representative.  The construction uses an oriented
copy of the representative; orientation does not change its carrier.
-/

/-- The tube whose orientation realizes `parentOrientedDirection`. -/
def parentOrientedTube {delta rho : NNReal}
    (parent : Tube rho) (owner : Tube delta) : Tube delta :=
  if ‖owner.axis.direction - parent.axis.direction‖ ≤ 14 * (rho : Real) then
    owner
  else
    reversedTube owner

@[simp]
theorem parentOrientedTube_carrier
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) :
    (parentOrientedTube parent owner).carrier = owner.carrier := by
  rw [parentOrientedTube]
  split_ifs
  · rfl
  · exact reversedTubeCarrier owner

@[simp]
theorem parentOrientedTube_midpoint
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) :
    tubeAxisMidpoint (parentOrientedTube parent owner) =
      tubeAxisMidpoint owner := by
  rw [parentOrientedTube]
  split_ifs
  · rfl
  · simp only [tubeAxisMidpoint, reversedTube, reversedUnitSegmentBase,
      reversedUnitSegmentDirection, UnitSegment.endpoint]
    module

@[simp]
theorem parentOrientedTube_direction
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) :
    (parentOrientedTube parent owner).axis.direction =
      parentOrientedDirection parent owner := by
  simp only [parentOrientedTube, parentOrientedDirection]
  split_ifs <;> rfl

private theorem sq_le_sq_of_abs_le {x a : Real} (h : |x| ≤ a) :
    x ^ 2 ≤ a ^ 2 := by
  have ha : 0 ≤ a := (abs_nonneg x).trans h
  have hsquare := (sq_le_sq₀ (abs_nonneg x) ha).2 h
  simpa only [sq_abs] using hsquare

/-- A three-vector whose coordinate differences are `< r` has distance at
most `2r`.  The slightly wasteful constant avoids square roots. -/
theorem dist_le_two_mul_of_coordinate_lt
    {v w : Space} {r : Real} (hr : 0 ≤ r)
    (hcoord : ∀ j : Fin 3, |v j - w j| < r) :
    dist v w ≤ 2 * r := by
  have h0 := sq_le_sq_of_abs_le (hcoord (0 : Fin 3)).le
  have h1 := sq_le_sq_of_abs_le (hcoord (1 : Fin 3)).le
  have h2 := sq_le_sq_of_abs_le (hcoord (2 : Fin 3)).le
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  nlinarith [sq_nonneg r]

/-- Equal split codes give physical (unnormalized) coordinate bounds. -/
theorem parentFrameCode_eq_physical_coordinate_close
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    |parentFrameLongitudinalOffset parent (owner p) -
        parentFrameLongitudinalOffset parent (owner q)| < (rho : Real) ∧
      (∀ j : Fin 3,
        |parentFrameTransverseOffset parent (owner p) j -
          parentFrameTransverseOffset parent (owner q) j| < (rho : Real)) ∧
      ∀ j : Fin 3,
        |parentOrientedDirection parent (owner p) j -
          parentOrientedDirection parent (owner q) j| < (rho : Real) := by
  have hclose := parentFrameCode_eq_coordinate_close hrhoPos parent owner
    hlong hdirection htransverse hcode
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrhoPos
  have hphysical {a b : Real}
      (h : |a / (rho : Real) - b / (rho : Real)| < 1) :
      |a - b| < (rho : Real) := by
    rw [← sub_div, abs_div, abs_of_pos hrhoReal] at h
    exact (div_lt_one hrhoReal).mp h
  refine ⟨hclose.1, ?_, ?_⟩
  · intro j
    fin_cases j
    · apply hphysical
      simpa [parentFrameShapeCoordinates] using hclose.2 (0 : Fin 6)
    · apply hphysical
      simpa [parentFrameShapeCoordinates] using hclose.2 (1 : Fin 6)
    · apply hphysical
      simpa [parentFrameShapeCoordinates] using hclose.2 (2 : Fin 6)
  · intro j
    fin_cases j
    · apply hphysical
      have h := hclose.2 (3 : Fin 6)
      simp [parentFrameShapeCoordinates] at h
      have h' :
          |parentOrientedDirection parent (owner p) 0 / (rho : Real) -
            parentOrientedDirection parent (owner q) 0 / (rho : Real)| < 1 := by
        convert h using 1
        congr 1
        ring
      exact h'
    · apply hphysical
      have h := hclose.2 (4 : Fin 6)
      simp [parentFrameShapeCoordinates] at h
      have h' :
          |parentOrientedDirection parent (owner p) 1 / (rho : Real) -
            parentOrientedDirection parent (owner q) 1 / (rho : Real)| < 1 := by
        convert h using 1
        congr 1
        ring
      exact h'
    · apply hphysical
      have h := hclose.2 (5 : Fin 6)
      simp [parentFrameShapeCoordinates] at h
      have h' :
          |parentOrientedDirection parent (owner p) 2 / (rho : Real) -
            parentOrientedDirection parent (owner q) 2 / (rho : Real)| < 1 := by
        convert h using 1
        congr 1
        ring
      exact h'

theorem parentFrameCode_eq_transverse_direction_dist_le
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    dist (parentFrameTransverseOffset parent (owner p))
        (parentFrameTransverseOffset parent (owner q)) ≤ 2 * (rho : Real) ∧
      dist (parentOrientedDirection parent (owner p))
        (parentOrientedDirection parent (owner q)) ≤ 2 * (rho : Real) := by
  have hphysical := parentFrameCode_eq_physical_coordinate_close hrhoPos
    parent owner hlong hdirection htransverse hcode
  exact ⟨
    dist_le_two_mul_of_coordinate_lt (NNReal.zero_le_coe) hphysical.2.1,
    dist_le_two_mul_of_coordinate_lt (NNReal.zero_le_coe) hphysical.2.2⟩

/-- Parent-frame transverse plus longitudinal coordinates reconstruct the
midpoint displacement. -/
theorem midpoint_sub_parent_eq_parentFrame_decomposition
    {delta rho : NNReal} (parent : Tube rho) (owner : Tube delta) :
    tubeAxisMidpoint owner - tubeAxisMidpoint parent =
      parentFrameTransverseOffset parent owner +
        (parentFrameLongitudinalOffset parent owner) •
          parent.axis.direction := by
  simp only [parentFrameTransverseOffset, parentFrameLongitudinalOffset,
    Family8PaperConflictProjectionStabilityV2.transverseResidual]
  module

theorem parentFrameCode_eq_midpoint_dist_le_three_mul
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    dist (tubeAxisMidpoint (owner p)) (tubeAxisMidpoint (owner q)) ≤
      3 * (rho : Real) := by
  have hphysical := parentFrameCode_eq_physical_coordinate_close hrhoPos
    parent owner hlong hdirection htransverse hcode
  have hdist := (parentFrameCode_eq_transverse_direction_dist_le hrhoPos
    parent owner hlong hdirection htransverse hcode).1
  have hp :=
    midpoint_sub_parent_eq_parentFrame_decomposition parent (owner p)
  have hq :=
    midpoint_sub_parent_eq_parentFrame_decomposition parent (owner q)
  have hvec :
      tubeAxisMidpoint (owner p) - tubeAxisMidpoint (owner q) =
        (parentFrameTransverseOffset parent (owner p) -
          parentFrameTransverseOffset parent (owner q)) +
        (parentFrameLongitudinalOffset parent (owner p) -
          parentFrameLongitudinalOffset parent (owner q)) •
            parent.axis.direction := by
    calc
      tubeAxisMidpoint (owner p) - tubeAxisMidpoint (owner q) =
          (tubeAxisMidpoint (owner p) - tubeAxisMidpoint parent) -
            (tubeAxisMidpoint (owner q) - tubeAxisMidpoint parent) := by
              module
      _ = (parentFrameTransverseOffset parent (owner p) +
            (parentFrameLongitudinalOffset parent (owner p)) •
              parent.axis.direction) -
          (parentFrameTransverseOffset parent (owner q) +
            (parentFrameLongitudinalOffset parent (owner q)) •
              parent.axis.direction) := by rw [hp, hq]
      _ = _ := by module
  rw [dist_eq_norm, hvec]
  calc
    ‖(parentFrameTransverseOffset parent (owner p) -
          parentFrameTransverseOffset parent (owner q)) +
        (parentFrameLongitudinalOffset parent (owner p) -
          parentFrameLongitudinalOffset parent (owner q)) •
            parent.axis.direction‖ ≤
        ‖parentFrameTransverseOffset parent (owner p) -
          parentFrameTransverseOffset parent (owner q)‖ +
        ‖(parentFrameLongitudinalOffset parent (owner p) -
          parentFrameLongitudinalOffset parent (owner q)) •
            parent.axis.direction‖ := norm_add_le _ _
    _ = dist (parentFrameTransverseOffset parent (owner p))
          (parentFrameTransverseOffset parent (owner q)) +
        |parentFrameLongitudinalOffset parent (owner p) -
          parentFrameLongitudinalOffset parent (owner q)| := by
      rw [dist_eq_norm, norm_smul, Real.norm_eq_abs,
        parent.axis.norm_direction, mul_one]
    _ ≤ 2 * (rho : Real) + (rho : Real) :=
      add_le_add hdist hphysical.1.le
    _ = 3 * (rho : Real) := by ring

theorem parentFrameCode_eq_oriented_axisPoint_dist_le_four_mul
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    dist ((parentOrientedTube parent (owner p)).axis.base +
          t • (parentOrientedTube parent (owner p)).axis.direction)
        ((parentOrientedTube parent (owner q)).axis.base +
          t • (parentOrientedTube parent (owner q)).axis.direction) ≤
      4 * (rho : Real) := by
  let T := parentOrientedTube parent (owner p)
  let U := parentOrientedTube parent (owner q)
  let s : Real := t - (2 : Real)⁻¹
  have hs : |s| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> dsimp only [s] <;> norm_num at * <;> linarith [ht.1, ht.2]
  have hT : T.axis.base + t • T.axis.direction =
      tubeAxisMidpoint T + s • T.axis.direction := by
    simp only [tubeAxisMidpoint, s]
    module
  have hU : U.axis.base + t • U.axis.direction =
      tubeAxisMidpoint U + s • U.axis.direction := by
    simp only [tubeAxisMidpoint, s]
    module
  have hmid : dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) ≤
      3 * (rho : Real) := by
    simpa only [T, U, parentOrientedTube_midpoint] using
      parentFrameCode_eq_midpoint_dist_le_three_mul hrhoPos parent owner
        hlong hdirection htransverse hcode
  have hdir : dist T.axis.direction U.axis.direction ≤ 2 * (rho : Real) := by
    simpa only [T, U, parentOrientedTube_direction] using
      (parentFrameCode_eq_transverse_direction_dist_le hrhoPos parent owner
        hlong hdirection htransverse hcode).2
  rw [hT, hU, dist_eq_norm]
  have hvec :
      (tubeAxisMidpoint T + s • T.axis.direction) -
          (tubeAxisMidpoint U + s • U.axis.direction) =
        (tubeAxisMidpoint T - tubeAxisMidpoint U) +
          s • (T.axis.direction - U.axis.direction) := by
    module
  rw [hvec]
  calc
    ‖(tubeAxisMidpoint T - tubeAxisMidpoint U) +
        s • (T.axis.direction - U.axis.direction)‖ ≤
      ‖tubeAxisMidpoint T - tubeAxisMidpoint U‖ +
        ‖s • (T.axis.direction - U.axis.direction)‖ := norm_add_le _ _
    _ = dist (tubeAxisMidpoint T) (tubeAxisMidpoint U) +
        |s| * dist T.axis.direction U.axis.direction := by
      rw [dist_eq_norm, dist_eq_norm, norm_smul, Real.norm_eq_abs]
    _ ≤ 3 * (rho : Real) + (2 : Real)⁻¹ * (2 * (rho : Real)) := by
      exact add_le_add hmid
        (mul_le_mul hs hdir dist_nonneg (by norm_num))
    _ = 4 * (rho : Real) := by ring

theorem parentFrameCode_eq_oriented_axis_carrier_subset_four_mul
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    (parentOrientedTube parent (owner p)).axis.carrier ⊆
      Metric.cthickening (4 * (rho : Real))
        (parentOrientedTube parent (owner q)).axis.carrier := by
  intro x hx
  rw [(parentOrientedTube parent (owner p)).axis.carrier_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact Metric.mem_cthickening_of_dist_le
    ((parentOrientedTube parent (owner p)).axis.base +
      t • (parentOrientedTube parent (owner p)).axis.direction)
    ((parentOrientedTube parent (owner q)).axis.base +
      t • (parentOrientedTube parent (owner q)).axis.direction)
    (4 * (rho : Real))
    (parentOrientedTube parent (owner q)).axis.carrier
    ((parentOrientedTube parent (owner q)).axis.mem_carrier_of_mem_Icc ht)
    (parentFrameCode_eq_oriented_axisPoint_dist_le_four_mul hrhoPos parent
      owner hlong hdirection htransverse hcode ht)

/-- Every original owner in one code cell lies in the genuine 5*rho tube
around an oriented representative owner.  This is the literal coarse-tube
containment that was not present in the finite-code layer. -/
theorem parentFrameCode_eq_owner_carrier_subset_five_mul
    {delta rho : NNReal} (hrhoPos : 0 < rho) (hdeltaRho : delta ≤ rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      FamilyStickyTubeParentDirectionCoherenceV1.UnorientedDirectionClose
        (owner p).axis parent.axis (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    (owner p).carrier ⊆
      ((parentOrientedTube parent (owner q)).changeRadius (5 * rho)).carrier := by
  let T := parentOrientedTube parent (owner p)
  let U := parentOrientedTube parent (owner q)
  have haxis : T.axis.carrier ⊆
      Metric.cthickening (4 * (rho : Real)) U.axis.carrier := by
    simpa only [T, U] using
      parentFrameCode_eq_oriented_axis_carrier_subset_four_mul hrhoPos parent
        owner hlong hdirection htransverse hcode
  have hthick :=
    Metric.cthickening_subset_of_subset (delta : Real) haxis
  rw [cthickening_cthickening (by positivity) (by positivity)] at hthick
  have hsum :
      (delta : Real) + 4 * (rho : Real) ≤ ((5 * rho : NNReal) : Real) := by
    have hdeltaRhoReal : (delta : Real) ≤ (rho : Real) := by
      exact_mod_cast hdeltaRho
    push_cast
    nlinarith
  have hmono :
      Metric.cthickening ((delta : Real) + 4 * (rho : Real)) U.axis.carrier ⊆
        Metric.cthickening (((5 * rho : NNReal) : Real)) U.axis.carrier :=
    Metric.cthickening_mono hsum U.axis.carrier
  rw [← parentOrientedTube_carrier parent (owner p)]
  change Metric.cthickening (delta : Real) T.axis.carrier ⊆
    Metric.cthickening (((5 * rho : NNReal) : Real)) U.axis.carrier
  exact hthick.trans hmono

#print axioms parentFrameCode_eq_oriented_axis_carrier_subset_four_mul
#print axioms parentFrameCode_eq_owner_carrier_subset_five_mul

#print axioms parentOrientedTube_carrier
#print axioms dist_le_two_mul_of_coordinate_lt
#print axioms parentFrameCode_eq_physical_coordinate_close
#print axioms parentFrameCode_eq_transverse_direction_dist_le
#print axioms midpoint_sub_parent_eq_parentFrame_decomposition
#print axioms parentFrameCode_eq_midpoint_dist_le_three_mul
#print axioms parentFrameCode_eq_oriented_axisPoint_dist_le_four_mul

end
end Family8PaperConflictOwnerParentFramePhysicalBridgeV5

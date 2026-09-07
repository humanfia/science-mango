import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyParentHullVolumeBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1

noncomputable section

/-!
# An automatic constant volume bound for a Sticky parent hull

Every active coarse parent contains a fine child.  The fine child supplies a
point in the unit ball, while the diameter of a radius-at-most-one tube is at
most three.  Hence every active coarse body lies in the radius-four ball and
so does their full convex hull.  This removes the parent-hull callback from
the popular-row factor.
-/

/-- The radius-four closed ball as a convex body. -/
def closedBallFourBody : ConvexBody Space where
  carrier := Metric.closedBall (0 : Space) 4
  convex' := convex_closedBall (0 : Space) 4
  isCompact' := isCompact_closedBall (0 : Space) 4
  nonempty' := ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

@[simp] theorem coe_closedBallFourBody :
    (closedBallFourBody : Set Space) = Metric.closedBall (0 : Space) 4 :=
  rfl

/-- Each active parent lies in the fixed radius-four ball. -/
theorem activeCoarseFamily_body_subset_closedBall_four
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (S.activeCoarseFamily k : Set Space) ⊆
      Metric.closedBall (0 : Space) 4 := by
  obtain ⟨i, hiActive, hparent⟩ :=
    S.parent_surjective k.1 k.2
  let p : Space := (D.family.tubes i).axis.base
  have hpFine : p ∈ (D.family.tubes i).carrier := by
    exact (D.family.tubes i).axis_subset_carrier
      (D.family.tubes i).axis.base_mem_carrier
  have hpUnit : p ∈ Metric.closedBall (0 : Space) 1 :=
    hD.contained_in_unit_ball i hpFine
  have hpCoarse : p ∈ (S.coarse.tubes k.1).carrier := by
    simpa only [hparent] using S.carrier_subset i hiActive hpFine
  intro y hy
  change y ∈ (S.coarse.tubes k.1).carrier at hy
  have hdiam : dist y p ≤ 1 + 2 * (rho : Real) :=
    dist_le_one_add_two_mul_radius_of_mem_tube_carrier
      (S.coarse.tubes k.1) hy hpCoarse
  have hrhoReal : (rho : Real) ≤ 1 := by
    exact_mod_cast hrhoOne
  rw [Metric.mem_closedBall] at hpUnit ⊢
  calc
    dist y 0 ≤ dist y p + dist p 0 := dist_triangle _ _ _
    _ ≤ (1 + 2 * (rho : Real)) + 1 := add_le_add hdiam hpUnit
    _ ≤ 4 := by linarith

/-- The full convex hull of the active coarse family remains in that ball,
including the empty-family case of hullContainer. -/
theorem fullFamilyHullContainer_activeCoarseFamily_subset_closedBall_four
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho ≤ 1) :
    (fullFamilyHullContainer S.activeCoarseFamily : Set Space) ⊆
      Metric.closedBall (0 : Space) 4 := by
  classical
  unfold fullFamilyHullContainer
  by_cases hs :
      (Finset.univ : Finset {k // k ∈ S.activeCoarse}).Nonempty
  · simpa only [coe_closedBallFourBody] using
      (hullContainer_subset (K := closedBallFourBody)
        S.activeCoarseFamily hs
        (fun k _hk =>
          activeCoarseFamily_body_subset_closedBall_four
            D hD S hrhoOne k))
  · have hempty :
        (Finset.univ : Finset {k // k ∈ S.activeCoarse}) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty, coe_hullContainer_empty]
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact Metric.mem_closedBall_self (by norm_num)

/-- A deliberately coarse explicit numerical volume bound for the ball. -/
theorem volume_closedBall_zero_four_le_512 :
    volume (Metric.closedBall (0 : Space) 4) ≤ (512 : ENNReal) := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  norm_num
  have hreal : Real.pi * 4 / 3 ≤ 8 := by
    nlinarith [Real.pi_lt_four]
  have hcoeff := ENNReal.ofReal_le_ofReal hreal
  calc
    64 * ENNReal.ofReal (Real.pi * 4 / 3) ≤ 64 * 8 := by
      simpa [mul_comm] using
        mul_le_mul_left (a := (64 : ENNReal)) hcoeff
    _ = 512 := by norm_num

/-- The actual parent hull has uniformly bounded volume. -/
theorem volume_fullFamilyHullContainer_activeCoarseFamily_le_512
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrhoOne : rho ≤ 1) :
    volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space) ≤
      (512 : ENNReal) := by
  exact (measure_mono
    (fullFamilyHullContainer_activeCoarseFamily_subset_closedBall_four
      D hD S hrhoOne)).trans volume_closedBall_zero_four_le_512

#print axioms activeCoarseFamily_body_subset_closedBall_four
#print axioms fullFamilyHullContainer_activeCoarseFamily_subset_closedBall_four
#print axioms volume_closedBall_zero_four_le_512
#print axioms volume_fullFamilyHullContainer_activeCoarseFamily_le_512

end
end Family8StickyParentHullVolumeBoundV1

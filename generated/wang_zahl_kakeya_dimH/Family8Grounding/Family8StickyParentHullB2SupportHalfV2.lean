import Family8Grounding.Family8StickyParentHullVolumeBoundV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8StickyParentHullB2SupportHalfV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

noncomputable section

/-!
# Radius-four parent support from radius-two fine support

At a parent radius at most one half, a parent tube has diameter at most two.
If it contains a point of a fine child supported in `B(0,2)`, the whole
parent therefore lies in `B(0,4)`.  No fine-scale separation hypothesis is
used.
-/

/-- Every active parent lies in `B(0,4)` when the fine tubes lie in `B(0,2)`
and the parent radius is at most one half. -/
theorem activeCoarseFamily_body_subset_closedBall_four_of_fine_B2
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (hfineB2 : forall i,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    (S : StickyScaleCover fine rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (k : {k // k ∈ S.activeCoarse}) :
    (S.activeCoarseFamily k : Set Space) ⊆
      Metric.closedBall (0 : Space) 4 := by
  obtain ⟨i, hiActive, hparent⟩ := S.parent_surjective k.1 k.2
  let p : Space := (fine.tubes i).axis.base
  have hpFine : p ∈ (fine.tubes i).carrier := by
    exact (fine.tubes i).axis_subset_carrier
      (fine.tubes i).axis.base_mem_carrier
  have hpTwo : p ∈ Metric.closedBall (0 : Space) 2 :=
    hfineB2 i hpFine
  have hpCoarse : p ∈ (S.coarse.tubes k.1).carrier := by
    simpa only [hparent] using S.carrier_subset i hiActive hpFine
  intro y hy
  change y ∈ (S.coarse.tubes k.1).carrier at hy
  have hdiam : dist y p <= 1 + 2 * (rho : Real) :=
    dist_le_one_add_two_mul_radius_of_mem_tube_carrier
      (S.coarse.tubes k.1) hy hpCoarse
  have hrhoReal' :
      (rho : Real) <= (((2 : NNReal)⁻¹ : NNReal) : Real) := by
    exact_mod_cast hrhoHalf
  have hrhoReal : (rho : Real) <= 1 / 2 := by
    simpa using hrhoReal'
  rw [Metric.mem_closedBall] at hpTwo ⊢
  calc
    dist y 0 <= dist y p + dist p 0 := dist_triangle _ _ _
    _ <= (1 + 2 * (rho : Real)) + 2 := add_le_add hdiam hpTwo
    _ <= 4 := by linarith

#print axioms
  activeCoarseFamily_body_subset_closedBall_four_of_fine_B2

end
end Family8StickyParentHullB2SupportHalfV2

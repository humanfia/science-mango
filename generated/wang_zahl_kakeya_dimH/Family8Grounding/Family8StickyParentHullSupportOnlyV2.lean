import Family8Grounding.Family8StickyParentHullVolumeBoundV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8StickyParentHullSupportOnlyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

noncomputable section

/-!
# Parent support from the support field alone

The radius-four parent estimate never uses fine-scale separation.  This
version exposes its exact input: literal unit-ball containment of each fine
tube.  It is intentionally independent of `ActualTubeDatum.IsAdmissible`.
-/

/-- Every active parent lies in `B(0,4)` using only fine support and the
sticky child-to-parent containment. -/
theorem activeCoarseFamily_body_subset_closedBall_four_of_fine_contained
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (hfineContained : forall i,
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrhoOne : rho <= 1)
    (k : {k // k ∈ S.activeCoarse}) :
    (S.activeCoarseFamily k : Set Space) ⊆
      Metric.closedBall (0 : Space) 4 := by
  obtain ⟨i, hiActive, hparent⟩ := S.parent_surjective k.1 k.2
  let p : Space := (fine.tubes i).axis.base
  have hpFine : p ∈ (fine.tubes i).carrier := by
    exact (fine.tubes i).axis_subset_carrier
      (fine.tubes i).axis.base_mem_carrier
  have hpUnit : p ∈ Metric.closedBall (0 : Space) 1 :=
    hfineContained i hpFine
  have hpCoarse : p ∈ (S.coarse.tubes k.1).carrier := by
    simpa only [hparent] using S.carrier_subset i hiActive hpFine
  intro y hy
  change y ∈ (S.coarse.tubes k.1).carrier at hy
  have hdiam : dist y p <= 1 + 2 * (rho : Real) :=
    dist_le_one_add_two_mul_radius_of_mem_tube_carrier
      (S.coarse.tubes k.1) hy hpCoarse
  have hrhoReal : (rho : Real) <= 1 := by exact_mod_cast hrhoOne
  rw [Metric.mem_closedBall] at hpUnit ⊢
  calc
    dist y 0 <= dist y p + dist p 0 := dist_triangle _ _ _
    _ <= (1 + 2 * (rho : Real)) + 1 := add_le_add hdiam hpUnit
    _ <= 4 := by linarith

#print axioms
  activeCoarseFamily_body_subset_closedBall_four_of_fine_contained

end
end Family8StickyParentHullSupportOnlyV2

import FamilyStickyGrounding.FamilyStickyAdjacentScaleStepV2
import Submission.Kakeya.ConvexFactoring.IndexPartition

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyParentFiberMassDecompositionV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: actual parent/fiber mass decomposition

The active fine indices of a `StickyScaleCover` are grouped by its literal
parent map.  For every test convex body, its contained fine-body mass is the
sum of the corresponding contained masses in the actual parent fibers.
Consequently the fine concentration is the sum of the fiber concentrations.
No parent-scale thickening or volume comparison is assumed.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

def indexFactorization (S : StickyScaleCover fine rho) :
    IndexFactorization iota (Fin S.coarseCard) where
  fine := S.activeFine
  coarse := S.activeCoarse
  parent := S.parent
  parent_mem := S.parent_mem

theorem indexFactorization_fiber_eq (S : StickyScaleCover fine rho)
    (k : Fin S.coarseCard) :
    (indexFactorization S).fiber k = S.fiber k := by
  ext i
  rw [IndexFactorization.mem_fiber,
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.mem_fiber]
  rfl

noncomputable def containedFineWeight (fine : UniformTubeFamily delta iota)
    (K : ConvexBody Space) (i : iota) : ENNReal := by
  classical
  exact if (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) then
    MeasureTheory.volume (fine.bodyFamily i : Set Space)
  else 0

def activeFineMassInside (S : StickyScaleCover fine rho)
    (K : ConvexBody Space) : ENNReal :=
  ∑ i ∈ S.activeFine, containedFineWeight fine K i

def fiberMassInside (S : StickyScaleCover fine rho)
    (k : Fin S.coarseCard) (K : ConvexBody Space) : ENNReal :=
  ∑ i ∈ S.fiber k, containedFineWeight fine K i

/-- Exact finite parent/fiber regrouping of the contained active mass. -/
theorem activeFineMassInside_eq_sum_fiberMassInside
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    activeFineMassInside S K =
      ∑ k ∈ S.activeCoarse, fiberMassInside S k K := by
  unfold activeFineMassInside fiberMassInside
  calc
    (∑ i ∈ S.activeFine, containedFineWeight fine K i) =
        ∑ k ∈ S.activeCoarse,
          ∑ i ∈ (indexFactorization S).fiber k,
            containedFineWeight fine K i :=
      (indexFactorization S).sum_fiberwise (containedFineWeight fine K)
    _ = ∑ k ∈ S.activeCoarse,
          ∑ i ∈ S.fiber k, containedFineWeight fine K i := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [indexFactorization_fiber_eq]

theorem activeFineFamily_containedNumerator_eq
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    (∑ i ∈ containedIndices (activeFineFamily S) K,
        MeasureTheory.volume (activeFineFamily S i : Set Space)) =
      activeFineMassInside S K := by
  classical
  unfold containedIndices activeFineFamily activeFineMassInside
    containedFineWeight
  simp only [Finset.sum_filter]
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach S.activeFine (fun i =>
    if (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) then
      MeasureTheory.volume (fine.bodyFamily i : Set Space)
    else 0)

theorem fiberFamily_containedNumerator_eq
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (K : ConvexBody Space) :
    (∑ i ∈ containedIndices (S.fiberFamily k) K,
        MeasureTheory.volume (S.fiberFamily k i : Set Space)) =
      fiberMassInside S k K := by
  classical
  unfold FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.fiberFamily
    containedIndices fiberMassInside containedFineWeight
  simp only [Finset.sum_filter]
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach (S.fiber k) (fun i =>
    if (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) then
      MeasureTheory.volume (fine.bodyFamily i : Set Space)
    else 0)

/-- Fine concentration is exactly the finite sum of actual fiber
concentrations for the same test body. -/
theorem concentration_activeFineFamily_eq_sum_fiber
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    concentration (activeFineFamily S) K =
      ∑ k ∈ S.activeCoarse, concentration (S.fiberFamily k) K := by
  unfold concentration
  rw [activeFineFamily_containedNumerator_eq,
    activeFineMassInside_eq_sum_fiberMassInside]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fiberFamily_containedNumerator_eq, div_eq_mul_inv]

/-- Automatic coarse envelope.  Improving the parent-card factor to coarse
concentration is the remaining thickened-test-body geometric step. -/
theorem concentration_activeFineFamily_le_card_mul_fiberDeltaMax
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    concentration (activeFineFamily S) K ≤
      S.activeCoarse.card • fiberDeltaMax S := by
  rw [concentration_activeFineFamily_eq_sum_fiber]
  apply Finset.sum_le_card_nsmul
  intro k hk
  exact (concentration_le_maximalConcentration (S.fiberFamily k) K).trans
    (maximalConcentration_fiber_le_fiberDeltaMax S ⟨k, hk⟩)

end StickyScaleCover

#print axioms StickyScaleCover.activeFineMassInside_eq_sum_fiberMassInside
#print axioms StickyScaleCover.concentration_activeFineFamily_eq_sum_fiber
#print axioms StickyScaleCover.concentration_activeFineFamily_le_card_mul_fiberDeltaMax

end
end FamilyStickyParentFiberMassDecompositionV6

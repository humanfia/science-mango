import FamilyStickyGrounding.FamilyStickyAdjacentTestBodyGeometryV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAdjacentNormalizedCrossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyParentFiberMassDecompositionV6.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: normalized adjacent cross estimate

This is the algebraic companion to the actual `K ↦ K^{+4ρ}` geometry.  Only
parents that really capture a fine tube contained in `K` contribute to the
fine concentration.  Their total contribution is bounded by the true fiber
`Delta_max`, while their total parent volume is bounded by the true coarse
`Delta_max` in the constructed thickening.

The output deliberately retains the ratio between the thickened-test-body
volume and a certified lower parent volume.  That is the source-faithful
factor which is meant to telescope between adjacent scales; it is not hidden
inside an assumed final cross bound.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- An uncaptured active parent contributes zero concentration to `K`. -/
theorem concentration_fiber_eq_zero_of_not_mem_capturedCoarseIndices
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (k : {k // k ∈ S.activeCoarse})
    (hk : k ∉ capturedCoarseIndices S K) :
    concentration (S.fiberFamily k.1) K = 0 := by
  classical
  have hempty : containedIndices (S.fiberFamily k.1) K = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    apply hk
    rw [mem_capturedCoarseIndices]
    have hiK : (S.fiberFamily k.1 i : Set Space) ⊆ (K : Set Space) := by
      simpa only [containedIndices, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    have hifiber := (S.mem_fiber i.1 k.1).mp i.2
    refine ⟨i.1, hifiber.1, hifiber.2, ?_⟩
    exact hiK
  simp [concentration, hempty]

/-- Exact restriction of the parent/fiber mass decomposition to the parents
that actually capture a fine tube inside `K`. -/
theorem concentration_activeFineFamily_eq_sum_captured
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    concentration (activeFineFamily S) K =
      ∑ k ∈ capturedCoarseIndices S K,
        concentration (S.fiberFamily k.1) K := by
  rw [concentration_activeFineFamily_eq_sum_fiber]
  have hattach :
      (∑ k ∈ S.activeCoarse, concentration (S.fiberFamily k) K) =
        ∑ k : {k // k ∈ S.activeCoarse},
          concentration (S.fiberFamily k.1) K := by
    rw [← Finset.attach_eq_univ]
    exact (Finset.sum_attach S.activeCoarse
      (fun k => concentration (S.fiberFamily k) K)).symm
  rw [hattach]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hkUniv hkCaptured
  exact concentration_fiber_eq_zero_of_not_mem_capturedCoarseIndices
    S K k hkCaptured

/-- Captured fine concentration is at most the actual number of captured
parents times the actual worst fiber `Delta_max`. -/
theorem concentration_activeFineFamily_le_captured_card_nsmul_fiberDeltaMax
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    concentration (activeFineFamily S) K ≤
      (capturedCoarseIndices S K).card • fiberDeltaMax S := by
  rw [concentration_activeFineFamily_eq_sum_captured]
  apply Finset.sum_le_card_nsmul
  intro k hk
  exact (concentration_le_maximalConcentration (S.fiberFamily k.1) K).trans
    (maximalConcentration_fiber_le_fiberDeltaMax S k)

/-- A uniform lower bound `parentFloor` for the volumes of captured parents
turns the coarse concentration estimate into a normalized captured-card
bound. -/
theorem captured_card_nsmul_parentFloor_div_thickening_le_coarseDeltaMax
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (parentFloor : ENNReal)
    (hfloor : ∀ k ∈ capturedCoarseIndices S K,
      parentFloor ≤
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) :
    ((capturedCoarseIndices S K).card • parentFloor) /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) ≤
      coarseDeltaMax S := by
  have hsum :
      (capturedCoarseIndices S K).card • parentFloor ≤
        ∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) := by
    calc
      (capturedCoarseIndices S K).card • parentFloor =
          ∑ _k ∈ capturedCoarseIndices S K, parentFloor := by simp
      _ ≤ ∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) :=
        Finset.sum_le_sum fun k hk => hfloor k hk
  exact (ENNReal.div_le_div_right hsum _).trans
    (capturedCoarseVolume_div_thickening_le_coarseDeltaMax S K)


/-- Actual normalized adjacent cross estimate, retaining the volume ratio
that telescopes between scales. -/
theorem normalized_adjacent_cross_le
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (parentFloor : ENNReal)
    (hfloor : ∀ k ∈ capturedCoarseIndices S K,
      parentFloor ≤
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) :
    concentration (activeFineFamily S) K * parentFloor /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) ≤
      fiberDeltaMax S * coarseDeltaMax S := by
  have hfine :=
    concentration_activeFineFamily_le_captured_card_nsmul_fiberDeltaMax S K
  have hcoarse :=
    captured_card_nsmul_parentFloor_div_thickening_le_coarseDeltaMax
      S K parentFloor hfloor
  calc
    concentration (activeFineFamily S) K * parentFloor /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) ≤
      ((capturedCoarseIndices S K).card • fiberDeltaMax S) * parentFloor /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) := by
        gcongr
    _ = fiberDeltaMax S *
        (((capturedCoarseIndices S K).card • parentFloor) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space)) := by
      simp only [nsmul_eq_mul, div_eq_mul_inv]
      ring
    _ ≤ fiberDeltaMax S * coarseDeltaMax S := by
      gcongr


/-- For actual rho-tubes, the parent-volume floor is automatic when
rho is at most one half. -/
theorem normalized_adjacent_cross_actual_tubes_le
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (hrho : rho ≤ (2 : NNReal)⁻¹) :
    concentration (activeFineFamily S) K *
        ((rho : ENNReal) ^ 2 / 2) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) ≤
      fiberDeltaMax S * coarseDeltaMax S := by
  apply normalized_adjacent_cross_le S K ((rho : ENNReal) ^ 2 / 2)
  intro k hk
  change ((rho : ENNReal) ^ 2 / 2) ≤
    MeasureTheory.volume (S.coarse.tubes k.1).carrier
  exact (S.coarse.tubes k.1).half_sq_le_volume_of_le_half hrho

end StickyScaleCover

#print axioms StickyScaleCover.concentration_fiber_eq_zero_of_not_mem_capturedCoarseIndices
#print axioms StickyScaleCover.concentration_activeFineFamily_eq_sum_captured
#print axioms StickyScaleCover.concentration_activeFineFamily_le_captured_card_nsmul_fiberDeltaMax
#print axioms StickyScaleCover.captured_card_nsmul_parentFloor_div_thickening_le_coarseDeltaMax
#print axioms StickyScaleCover.normalized_adjacent_cross_le
#print axioms StickyScaleCover.normalized_adjacent_cross_actual_tubes_le

end
end FamilyStickyAdjacentNormalizedCrossV1

import FamilyStickyGrounding.FamilyStickyScaleChainNormalizedIntegrationV1
import FamilyStickyGrounding.FamilyStickyAdjacentNormalizedCrossV1
import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy
import Submission.Kakeya.ConvexFactoring.NonConcentration

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainBufferedHierarchyNormalizedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover
open FamilyStickyAdjacentNormalizedCrossV1.StickyScaleCover
open FamilyStickyScaleChainNormalizedIntegrationV1

noncomputable section

/-!
# Sticky Kakeya: buffered hierarchy and normalized adjacent steps

Common-fine-tube geometry only puts a raw child in a thickening of its raw
parent.  The repository's `MultiscaleTubeHierarchy` records this cost and
recursively buffers every level, producing exact partitions at the effective
radii.  This module converts those partitions to literal Sticky covers.

It also strengthens the frozen normalized cross estimate by retaining the
actual coarse concentration in the constructed thickened body.  A general
volume-envelope lemma then puts precisely the normalization needed by the
telescoping chain on both sides.  The envelope factor remains visible as a
local dimensional loss.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Forget the branching bounds of an exact coarse partition while retaining
its literal active families, parent map, surjectivity, and containment. -/
def ofCoarseTubePartition {coarseCard : Nat}
    {coarse : UniformTubeFamily rho (Fin coarseCard)}
    (P : CoarseTubePartition fine coarse) : StickyScaleCover fine rho where
  coarseCard := coarseCard
  coarse := coarse
  activeFine := fine.refinement.refined
  activeCoarse := coarse.refinement.refined
  parent := P.index.parent
  activeFine_eq_refined := rfl
  activeCoarse_eq_refined := rfl
  parent_mem := by
    intro i hi
    have hi' : i ∈ P.index.fine := by
      rw [P.fine_eq_refined]
      exact hi
    have hp := P.index.parent_mem i hi'
    rw [P.coarse_eq_refined] at hp
    exact hp
  parent_surjective := by
    intro k hk
    have hk' : k ∈ P.index.coarse := by
      rw [P.coarse_eq_refined]
      exact hk
    obtain ⟨i, hi, hparent⟩ := P.parent_surjective k hk'
    refine ⟨i, ?_, hparent⟩
    rw [← P.fine_eq_refined]
    exact hi
  carrier_subset := by
    intro i hi
    apply P.carrier_subset i
    rw [P.fine_eq_refined]
    exact hi

/-- The normalized captured-parent count is bounded by the actual coarse
concentration in the constructed thickening, before taking its supremum. -/
theorem captured_card_nsmul_parentFloor_div_thickening_le_coarseConcentration
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (parentFloor : ENNReal)
    (hfloor : ∀ k ∈ capturedCoarseIndices S K,
      parentFloor <=
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) :
    ((capturedCoarseIndices S K).card • parentFloor) /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
      concentration S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) := by
  have hsum :
      (capturedCoarseIndices S K).card • parentFloor <=
        ∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) := by
    calc
      (capturedCoarseIndices S K).card • parentFloor =
          ∑ _k ∈ capturedCoarseIndices S K, parentFloor := by simp
      _ <= ∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) :=
        Finset.sum_le_sum fun k hk => hfloor k hk
  have hcontained :
      (∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) <=
        ∑ k ∈ containedIndices S.activeCoarseFamily
            (closedThickeningBody K (4 * rho)),
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) :=
    Finset.sum_le_sum_of_subset
      (capturedCoarseIndices_subset_containedIndices S K)
  calc
    ((capturedCoarseIndices S K).card • parentFloor) /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
      (∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) :=
      ENNReal.div_le_div_right hsum _
    _ <=
      (∑ k ∈ containedIndices S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)),
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) :=
      ENNReal.div_le_div_right hcontained _
    _ = concentration S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) := rfl

/-- The source-faithful adjacent estimate before replacing the constructed
coarse concentration by a global maximum. -/
theorem normalized_adjacent_cross_to_thickening_le
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (parentFloor : ENNReal)
    (hfloor : ∀ k ∈ capturedCoarseIndices S K,
      parentFloor <=
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) :
    concentration (activeFineFamily S) K * parentFloor /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
      fiberDeltaMax S *
        concentration S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)) := by
  have hfine :=
    concentration_activeFineFamily_le_captured_card_nsmul_fiberDeltaMax S K
  have hcoarse :=
    captured_card_nsmul_parentFloor_div_thickening_le_coarseConcentration
      S K parentFloor hfloor
  calc
    concentration (activeFineFamily S) K * parentFloor /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
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
    _ <= fiberDeltaMax S *
        concentration S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)) := by
      gcongr

/-- If the current test-body volume is at most `dimensionalLoss` times its
declared tube normalization, the actual parent-volume floor produces the
two-sided normalized step required by the telescoping chain. -/
theorem normalized_adjacent_cross_with_volumeEnvelope_le
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (currentTube nextTube dimensionalLoss : ENNReal)
    (hscale0 : dimensionalLoss * currentTube ≠ 0)
    (hscaleTop : dimensionalLoss * currentTube ≠ ∞)
    (hbody : MeasureTheory.volume (K : Set Space) <=
      dimensionalLoss * currentTube)
    (hnext : ∀ k ∈ capturedCoarseIndices S K,
      nextTube <=
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) :
    concentration (activeFineFamily S) K * nextTube /
        MeasureTheory.volume
          (closedThickeningBody K (4 * rho) : Set Space) <=
      (dimensionalLoss * fiberDeltaMax S) *
        (concentration S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)) * currentTube /
            MeasureTheory.volume (K : Set Space)) := by
  by_cases hbody0 : MeasureTheory.volume (K : Set Space) = 0
  · have hconcentration0 : concentration (activeFineFamily S) K = 0 := by
      rw [concentration_eq_containedMass_div,
        containedMass_eq_zero_of_volume_eq_zero (activeFineFamily S) K hbody0,
        hbody0]
      simp
    simp [hconcentration0]
  · have hbodyTop : MeasureTheory.volume (K : Set Space) ≠ ∞ :=
      K.isCompact.measure_lt_top.ne
    let scaledFloor : ENNReal :=
      nextTube * MeasureTheory.volume (K : Set Space) /
        (dimensionalLoss * currentTube)
    have hscaled_le_next : scaledFloor <= nextTube := by
      apply (ENNReal.div_le_iff_le_mul
        (Or.inl hscale0) (Or.inl hscaleTop)).2
      gcongr
    have hcross := normalized_adjacent_cross_to_thickening_le
      S K scaledFloor fun k hk => (hscaled_le_next.trans (hnext k hk))
    have hleft :
        (concentration (activeFineFamily S) K * scaledFloor /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space)) *
              (dimensionalLoss * currentTube) =
          (concentration (activeFineFamily S) K * nextTube /
            MeasureTheory.volume
              (closedThickeningBody K (4 * rho) : Set Space)) *
                MeasureTheory.volume (K : Set Space) := by
      calc
        _ = (concentration (activeFineFamily S) K * nextTube /
            MeasureTheory.volume
              (closedThickeningBody K (4 * rho) : Set Space)) *
            (MeasureTheory.volume (K : Set Space) /
              (dimensionalLoss * currentTube) *
                (dimensionalLoss * currentTube)) := by
          simp only [scaledFloor, div_eq_mul_inv]
          ring
        _ = _ := by
          rw [ENNReal.div_mul_cancel hscale0 hscaleTop]
    have hmul :
        (concentration (activeFineFamily S) K * nextTube /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space)) *
              MeasureTheory.volume (K : Set Space) <=
          (fiberDeltaMax S *
            concentration S.activeCoarseFamily
              (closedThickeningBody K (4 * rho))) *
                (dimensionalLoss * currentTube) := by
      rw [← hleft]
      gcongr
    have hdiv :
        concentration (activeFineFamily S) K * nextTube /
            MeasureTheory.volume
              (closedThickeningBody K (4 * rho) : Set Space) <=
          ((fiberDeltaMax S *
            concentration S.activeCoarseFamily
              (closedThickeningBody K (4 * rho))) *
                (dimensionalLoss * currentTube)) /
              MeasureTheory.volume (K : Set Space) :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hbody0) (Or.inl hbodyTop)).2 hmul
    calc
      concentration (activeFineFamily S) K * nextTube /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) <=
        ((fiberDeltaMax S *
          concentration S.activeCoarseFamily
            (closedThickeningBody K (4 * rho))) *
              (dimensionalLoss * currentTube)) /
            MeasureTheory.volume (K : Set Space) := hdiv
      _ = (dimensionalLoss * fiberDeltaMax S) *
          (concentration S.activeCoarseFamily
            (closedThickeningBody K (4 * rho)) * currentTube /
              MeasureTheory.volume (K : Set Space)) := by
        simp only [div_eq_mul_inv]
        ring

end StickyScaleCover

#print axioms StickyScaleCover.ofCoarseTubePartition
#print axioms StickyScaleCover.captured_card_nsmul_parentFloor_div_thickening_le_coarseConcentration
#print axioms StickyScaleCover.normalized_adjacent_cross_to_thickening_le
#print axioms StickyScaleCover.normalized_adjacent_cross_with_volumeEnvelope_le

end
end FamilyStickyScaleChainBufferedHierarchyNormalizedV1

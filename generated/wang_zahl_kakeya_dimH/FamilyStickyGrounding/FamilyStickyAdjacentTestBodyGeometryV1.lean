import FamilyStickyGrounding.FamilyStickyParentFiberMassDecompositionV6
import Submission.Kakeya.ConvexFactoring.TubeCommonSegment

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAdjacentTestBodyGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyParentFiberMassDecompositionV6.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: actual adjacent test-body geometry

This module implements the first genuinely geometric part of the
`K \mapsto K_m` argument in Lemma 7.2 of the streamlined proof.  The closed
metric thickening of a convex test body is again a convex body.  If a fine
tube is contained in `K`, then its actual coarse parent in a
`StickyScaleCover` is contained in the closed `4 rho`-thickening of `K`.

The factor four is not an assumption: it is supplied by the proved
common-fine-tube geometry in `TubeCommonSegment`.  No adjacent cross bound,
sticky conclusion, or final `Delta_max` inequality is used as a premise.
-/

/-- A compact convex body enlarged by a closed metric radius. -/
def closedThickeningBody (K : ConvexBody Space) (r : NNReal) : ConvexBody Space where
  carrier := Metric.cthickening (r : Real) (K : Set Space)
  convex' := K.convex.cthickening (r : Real)
  isCompact' := K.isCompact.cthickening
  nonempty' := K.nonempty.mono (Metric.self_subset_cthickening _)

@[simp] theorem coe_closedThickening (K : ConvexBody Space) (r : NNReal) :
    (closedThickeningBody K r : Set Space) =
      Metric.cthickening (r : Real) (K : Set Space) :=
  rfl

/-- Every convex body lies in each of its closed thickenings. -/
theorem subset_closedThickening (K : ConvexBody Space) (r : NNReal) :
    (K : Set Space) ⊆ (closedThickeningBody K r : Set Space) :=
  Metric.self_subset_cthickening _

/-- Closed thickening is monotone in the underlying body. -/
theorem closedThickening_mono {K L : ConvexBody Space} (r : NNReal)
    (hKL : (K : Set Space) ⊆ (L : Set Space)) :
    (closedThickeningBody K r : Set Space) ⊆
      (closedThickeningBody L r : Set Space) :=
  Metric.cthickening_subset_of_subset (r : Real) hKL

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The active coarse parents that have at least one fine child contained in
the test body.  The subtype keeps the parent tied to the actual active coarse
family, so it can be compared directly with `containedIndices`. -/
def capturedCoarseIndices (S : StickyScaleCover fine rho)
    (K : ConvexBody Space) : Finset {k // k ∈ S.activeCoarse} := by
  classical
  exact Finset.univ.filter fun k =>
    ∃ i, i ∈ S.activeFine ∧ S.parent i = k.1 ∧
      (fine.tubes i).carrier ⊆ (K : Set Space)

@[simp] theorem mem_capturedCoarseIndices
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (k : {k // k ∈ S.activeCoarse}) :
    k ∈ capturedCoarseIndices S K ↔
      ∃ i, i ∈ S.activeFine ∧ S.parent i = k.1 ∧
        (fine.tubes i).carrier ⊆ (K : Set Space) := by
  classical
  simp [capturedCoarseIndices]

/-- A coarse parent of a fine tube captured by `K` lies in the actual
`4 rho` closed thickening of `K`. -/
theorem coarse_parent_subset_four_rho_closedThickening
    (S : StickyScaleCover fine rho) (K : ConvexBody Space)
    (i : iota) (hi : i ∈ S.activeFine)
    (hiK : (fine.tubes i).carrier ⊆ (K : Set Space)) :
    (S.coarse.tubes (S.parent i)).carrier ⊆
      (closedThickeningBody K (4 * rho) : Set Space) := by
  have hraw :
      (S.coarse.tubes (S.parent i)).carrier ⊆
        Metric.cthickening (4 * (rho : Real)) (fine.tubes i).carrier :=
    Tube.carrier_subset_four_mul_cthickening_of_commonFineTube
      (fine.tubes i) (S.coarse.tubes (S.parent i)) (fine.tubes i)
      (S.carrier_subset i hi) (by exact Subset.rfl)
  have hmono := Metric.cthickening_subset_of_subset
    (4 * (rho : Real)) hiK
  exact hraw.trans (by
    simpa [closedThickeningBody, NNReal.coe_mul] using hmono)

/-- Every captured active parent is one of the coarse bodies contained in the
geometrically constructed thickened test body. -/
theorem capturedCoarseIndices_subset_containedIndices
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    capturedCoarseIndices S K ⊆
      containedIndices S.activeCoarseFamily
        (closedThickeningBody K (4 * rho)) := by
  classical
  intro k hk
  obtain ⟨ i, hi, hparent, hiK ⟩ :=
    (mem_capturedCoarseIndices S K k).mp hk
  simp only [containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  change (S.coarse.tubes k.1).carrier ⊆ _
  rw [show k.1 = S.parent i by exact hparent.symm]
  exact coarse_parent_subset_four_rho_closedThickening S K i hi hiK

/-- The summed volume of the captured parents is controlled by the literal
coarse concentration in the constructed `4 rho` thickening. -/
theorem capturedCoarseVolume_div_thickening_le_coarseDeltaMax
    (S : StickyScaleCover fine rho) (K : ConvexBody Space) :
    (∑ k ∈ capturedCoarseIndices S K,
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) ≤
      coarseDeltaMax S := by
  have hsum :
      (∑ k ∈ capturedCoarseIndices S K,
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) ≤
        ∑ k ∈ containedIndices S.activeCoarseFamily
            (closedThickeningBody K (4 * rho)),
          MeasureTheory.volume (S.activeCoarseFamily k : Set Space) := by
    exact Finset.sum_le_sum_of_subset
      (capturedCoarseIndices_subset_containedIndices S K)
  calc
    (∑ k ∈ capturedCoarseIndices S K,
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) ≤
      (∑ k ∈ containedIndices S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)),
        MeasureTheory.volume (S.activeCoarseFamily k : Set Space)) /
          MeasureTheory.volume
            (closedThickeningBody K (4 * rho) : Set Space) :=
      ENNReal.div_le_div_right hsum _
    _ = concentration S.activeCoarseFamily
          (closedThickeningBody K (4 * rho)) := rfl
    _ ≤ coarseDeltaMax S :=
      concentration_le_maximalConcentration S.activeCoarseFamily _

end StickyScaleCover

#print axioms closedThickeningBody
#print axioms StickyScaleCover.coarse_parent_subset_four_rho_closedThickening
#print axioms StickyScaleCover.capturedCoarseIndices_subset_containedIndices
#print axioms StickyScaleCover.capturedCoarseVolume_div_thickening_le_coarseDeltaMax

end
end FamilyStickyAdjacentTestBodyGeometryV1

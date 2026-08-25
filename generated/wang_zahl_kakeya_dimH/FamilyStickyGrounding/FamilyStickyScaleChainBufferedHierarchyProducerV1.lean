import FamilyStickyGrounding.FamilyStickyScaleChainBufferedHierarchyNormalizedV1

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainBufferedHierarchyProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyAdjacentTestBodyGeometryV1
open FamilyStickyAdjacentTestBodyGeometryV1.StickyScaleCover
open FamilyStickyScaleChainBufferedHierarchyNormalizedV1.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: automatic buffered-hierarchy producer

An `AdjacentTubeStep.commonFine` only supplies raw containment in a closed
neighborhood.  `MultiscaleTubeHierarchy` accumulates those neighborhoods as
buffers and produces exact partitions between its effective families.  This
module turns every such partition into an actual Sticky adjacent cover.

The resulting radii remain `nominalRadius + accumulatedBuffer`; no theorem
silently casts them back to the nominal scales.
-/

namespace MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}

/-- The recursively buffered exact partition as a literal Sticky cover. -/
def effectiveStickyScaleCover
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) :
    StickyScaleCover (H.effectiveFamily l) (H.effectiveRadius (l + 1)) :=
  FamilyStickyScaleChainBufferedHierarchyNormalizedV1.StickyScaleCover.ofCoarseTubePartition (H.effectivePartition l hl)

/-- The active convex family at one effective hierarchy level. -/
def effectiveActiveFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l))) (l : Nat) :
    ConvexFamily
      {i // i ∈ (H.effectiveFamily l).refinement.refined} :=
  fun i => (H.effectiveFamily l).bodyFamily i.1

@[simp] theorem effectiveStickyScaleCover_activeFineFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) :
    activeFineFamily (effectiveStickyScaleCover H l hl) =
      effectiveActiveFamily H l := by
  rfl

@[simp] theorem effectiveStickyScaleCover_activeCoarseFamily
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) :
    (effectiveStickyScaleCover H l hl).activeCoarseFamily =
      effectiveActiveFamily H (l + 1) := by
  rfl

/-- Adjacent effective covers share their middle active family literally. -/
theorem effective_coarseDeltaMax_eq_next_fineDeltaMax
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l + 1 < depth) :
    coarseDeltaMax
        (effectiveStickyScaleCover H l
          (lt_trans (Nat.lt_succ_self l) hl)) =
      fineDeltaMax (effectiveStickyScaleCover H (l + 1) hl) := by
  rfl

/-- The strengthened normalized cross estimate on an honest buffered step.
The common-fine cost is present in `effectiveRadius`; the volume-envelope
cost is the displayed `dimensionalLoss`. -/
theorem effective_normalized_adjacent_cross_with_volumeEnvelope_le
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) (K : ConvexBody Space)
    (currentTube nextTube dimensionalLoss : ENNReal)
    (hscale0 : dimensionalLoss * currentTube ≠ 0)
    (hscaleTop : dimensionalLoss * currentTube ≠ ∞)
    (hbody : MeasureTheory.volume (K : Set Space) <=
      dimensionalLoss * currentTube)
    (hnext : ∀ k ∈ capturedCoarseIndices
        (effectiveStickyScaleCover H l hl) K,
      nextTube <= MeasureTheory.volume
        ((effectiveStickyScaleCover H l hl).activeCoarseFamily k : Set Space)) :
    concentration (effectiveActiveFamily H l) K * nextTube /
        MeasureTheory.volume
          (closedThickeningBody K
            (4 * H.effectiveRadius (l + 1)) : Set Space) <=
      (dimensionalLoss * fiberDeltaMax
        (effectiveStickyScaleCover H l hl)) *
        (concentration (effectiveActiveFamily H (l + 1))
          (closedThickeningBody K
            (4 * H.effectiveRadius (l + 1))) * currentTube /
              MeasureTheory.volume (K : Set Space)) := by
  exact normalized_adjacent_cross_with_volumeEnvelope_le
    (effectiveStickyScaleCover H l hl) K currentTube nextTube
      dimensionalLoss hscale0 hscaleTop hbody hnext

/-- One-step expansion of the effective parent radius.  In particular the
raw common-fine cost and the previously accumulated buffer are explicit. -/
theorem effectiveRadius_succ_eq
    (H : MultiscaleTubeHierarchy depth nominalRadius
      (fun l => Fin (card l)))
    (l : Nat) (hl : l < depth) :
    H.effectiveRadius (l + 1) =
      nominalRadius (l + 1) +
        ((H.step l hl).rawCost + H.accumulatedBuffer l) := by
  rw [MultiscaleTubeHierarchy.effectiveRadius,
    H.accumulatedBuffer_succ l hl]

end MultiscaleTubeHierarchy

#print axioms MultiscaleTubeHierarchy.effectiveStickyScaleCover
#print axioms MultiscaleTubeHierarchy.effectiveStickyScaleCover_activeFineFamily
#print axioms MultiscaleTubeHierarchy.effective_coarseDeltaMax_eq_next_fineDeltaMax
#print axioms MultiscaleTubeHierarchy.effective_normalized_adjacent_cross_with_volumeEnvelope_le
#print axioms MultiscaleTubeHierarchy.effectiveRadius_succ_eq

end
end FamilyStickyScaleChainBufferedHierarchyProducerV1

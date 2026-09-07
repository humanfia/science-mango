import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
import Family8Grounding.Family8SelectedParentBlockDensityLocalCordobaV1

/-!
# Selected-parent block density bounded by its fibre cardinality

For a literal greedy occurrence block, containment in its winning body bounds
the ambient family-volume density by the number of members in its fibre.  The
selected-parent density identity then turns this into the corresponding bound
for the existing `blockDensity`.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CoreHighBlockDensityCardUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8PaperEq45MaxWitnessCanonicalDeltaUpperV1
open Family8SelectedParentBlockDensityLocalCordobaV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The density of a selected greedy block is at most the cardinality of its
literal fibre. -/
theorem selectedParent_blockDensity_le_fiberCard
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length) :
    blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q) ≤
      ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) := by
  have hbody0 :
      volume ((blockAt S.activeCoarseFamily P q).body : Set Space) ≠ 0 := by
    obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P q).fiber_nonempty
    have hcontained := (blockAt S.activeCoarseFamily P q).contained p hp
    have hpVolume :
        0 < volume (S.activeCoarseFamily p : Set Space) := by
      change 0 < volume (S.coarse.tubes p.1).carrier
      exact (S.coarse.tubes p.1).volume_pos hrho
    exact (hpVolume.trans_le (measure_mono hcontained)).ne'
  rw [← ambientFamilyVolumeDensity_selectedParentBlock_eq_blockDensity
    S P q]
  simpa only [Fintype.card_coe] using
    (ambientFamilyVolumeDensity_le_card
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q).fiber)
      (blockAt S.activeCoarseFamily P q).body
      (fun i =>
        (blockAt S.activeCoarseFamily P q).contained i.1 i.2)
      hbody0)

#print axioms selectedParent_blockDensity_le_fiberCard

end

end Family8CoreHighBlockDensityCardUpperV1

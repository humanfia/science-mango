import Family8Grounding.Family8SelectedParentBlockDensityLocalCordobaV1
import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2

/-!
# Finite nonzero block-density Katz--Tao bundle for one high occurrence

The same-core high branch already carries both strict high density and the
constant-one Frostman certificate of one literal greedy occurrence.  This
small successor packages the three scalar facts required by the local joint
residual consumer: the block density is nonzero, it is finite, and it is a
Katz--Tao constant for that same selected block.

No occurrence, block, or side bucket is selected here.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SelectedParentBlockDensityHighOccurrenceBundleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentBlockDensityLocalCordobaV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- On the literal block carried by a same-core high occurrence, the exact
block density is a finite nonzero Katz--Tao constant for that same block.
The conjunction order matches the scalar side conditions of the local joint
residual theorem. -/
theorem coreHighOccurrence_blockDensity_ne_zero_ne_top_and_isKatzTao
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (q : Fin (blocks S.activeCoarseFamily P).length)
    (hocc : CoreHighConcentrationOccurrence
      (activeParentActualTubeDatum S Y) P A q) :
    let d := blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q)
    d ≠ 0 ∧ d ≠ ∞ ∧
      IsKatzTao d
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P q).fiber) := by
  dsimp only
  unfold CoreHighConcentrationOccurrence at hocc
  simp only [activeParentActualTubeDatum_family_bodyFamily] at hocc
  have hhigh : A < blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q) := hocc.1
  have hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q) ≠ 0 :=
    (lt_of_le_of_lt bot_le hhigh).ne'
  have hbody0 :
      volume ((blockAt S.activeCoarseFamily P q).body : Set Space) ≠ 0 := by
    obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P q).fiber_nonempty
    have hcontained := (blockAt S.activeCoarseFamily P q).contained p hp
    have hpVolume :
        0 < volume (S.activeCoarseFamily p : Set Space) := by
      change 0 < volume (S.coarse.tubes p.1).carrier
      exact (S.coarse.tubes p.1).volume_pos hrho
    exact (hpVolume.trans_le (measure_mono hcontained)).ne'
  have hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q) ≠ ∞ := by
    have hfinite := ambientFamilyVolumeDensity_ne_top
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q).fiber)
      (blockAt S.activeCoarseFamily P q).body hbody0
    simpa only [
      ambientFamilyVolumeDensity_selectedParentBlock_eq_blockDensity]
      using hfinite
  have hF : IsFrostmanIn 1
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q).fiber)
      (blockAt S.activeCoarseFamily P q).body := by
    exact selectedParentBlock_isFrostmanIn_one S Y P q
  exact ⟨hd0, hdTop,
    selectedParentBlock_isKatzTao_blockDensity_of_isFrostmanIn_one
      S hrho P q hF⟩

#print axioms
  coreHighOccurrence_blockDensity_ne_zero_ne_top_and_isKatzTao

end
end Family8SelectedParentBlockDensityHighOccurrenceBundleV1

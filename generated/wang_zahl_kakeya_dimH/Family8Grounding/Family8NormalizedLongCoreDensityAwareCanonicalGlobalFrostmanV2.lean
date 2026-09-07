import Family8Grounding.Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanOnUnivV2
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

/-!
# Canonical global Frostman data on the selected long-core cover, V2

Fresh-build-safe successor with the canonical radius-four namespace opened
explicitly.  The selected exact-degree restriction remains in a successor.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareCanonicalGlobalFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActiveCoarseCanonicalFrostmanOnUnivV2
open Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyDensityAwareCanonicalLogSelectedDatumV2
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Admissibility of the retagged actual datum used by `S1`. -/
theorem coreDensityAwareSelectedActualDatum_isAdmissible
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (coreDensityAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).IsAdmissible := by
  unfold coreDensityAwareSelectedActualDatum
  exact ActualTubeDatum.IsAdmissible.densityAwareSelected
    hD
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    sourceA hsourceA hD.delta_pos
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (coreCanonicalBufferedGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)

/-- The canonical full active-coarse Frostman constant of `S1`. -/
noncomputable def coreDensityAwareCanonicalGlobalFrostmanConstant
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) : ENNReal :=
  canonicalFrostmanConstant
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).activeCoarseFamily
    closedBallFourBody

/-- The full active-coarse canonical Frostman theorem on the literal `S1`. -/
theorem coreDensityAwareCanonicalGlobalFrostman
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    IsFrostmanOn
      (coreDensityAwareCanonicalGlobalFrostmanConstant
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
      (coreDensityAwareSelectedStickyCover
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).activeCoarseFamily
      Finset.univ closedBallFourBody := by
  apply StickyScaleCover.activeCoarseFamily_isFrostmanOn_univ_canonical
    (coreDensityAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedActualDatum_isAdmissible
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (canonicalBufferedRadius_le_one
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
  exact
    (coreDensityAwareLogPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).coarseIndices_nonempty

/-- The canonical global constant is finite on the nonempty positive-radius
active coarse family. -/
theorem coreDensityAwareCanonicalGlobalFrostmanConstant_ne_top
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    coreDensityAwareCanonicalGlobalFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine ≠ ∞ := by
  let S1 := coreDensityAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine
  have hglobal := coreDensityAwareCanonicalGlobalFrostman
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine
  have hcontained : ∀ k,
      (S1.activeCoarseFamily k : Set Space) ⊆
        (closedBallFourBody : Set Space) := by
    intro k
    exact hglobal.1 k (Finset.mem_univ k)
  have hmass0 : containedMass S1.activeCoarseFamily closedBallFourBody ≠ 0 := by
    rw [containedMass_eq_familyVolume_of_contained
      S1.activeCoarseFamily closedBallFourBody hcontained]
    exact (activeCoarseFamilyVolume_pos S1
      (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      ((coreDensityAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).coarseIndices_nonempty)).ne'
  unfold coreDensityAwareCanonicalGlobalFrostmanConstant
  unfold canonicalFrostmanConstant
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top
      (maximalConcentration_lt_top S1.activeCoarseFamily).ne
      closedBallFourBody.isCompact.measure_lt_top.ne
  · exact hmass0

#print axioms coreDensityAwareSelectedActualDatum_isAdmissible
#print axioms coreDensityAwareCanonicalGlobalFrostmanConstant
#print axioms coreDensityAwareCanonicalGlobalFrostman
#print axioms coreDensityAwareCanonicalGlobalFrostmanConstant_ne_top

end
end Family8NormalizedLongCoreDensityAwareCanonicalGlobalFrostmanV2

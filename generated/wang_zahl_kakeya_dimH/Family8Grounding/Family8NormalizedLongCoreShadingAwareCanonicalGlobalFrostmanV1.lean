import Family8Grounding.Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanOnUnivV2
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

/-!
# Canonical global Frostman data on the shading-aware selected cover

The active coarse family of the literal shading-aware lower cover is finite,
nonempty, positive-radius, and contained in the canonical ambient ball.  Its
canonical global Frostman constant and finiteness are therefore intrinsic;
no external Frostman callback is used.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActiveCoarseCanonicalFrostmanOnUnivV2
open Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyShadingAwareCanonicalLogSelectedDatumV1
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

/-- Admissibility of the retagged shading-aware actual datum. -/
theorem coreShadingAwareSelectedActualDatum_isAdmissible
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    (coreShadingAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).IsAdmissible := by
  unfold coreShadingAwareSelectedActualDatum
  exact ActualTubeDatum.IsAdmissible.shadingAwareSelected
    hD
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by simpa only [coreShadingAwareActiveShadingMass] using hmass)

/-- Canonical global Frostman constant for the literal selected active coarse
family. -/
noncomputable def coreShadingAwareCanonicalGlobalFrostmanConstant
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) : ENNReal :=
  canonicalFrostmanConstant
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
      ).activeCoarseFamily
    closedBallFourBody

/-- Global normalized Frostman control on all active selected parents. -/
theorem coreShadingAwareCanonicalGlobalFrostman
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    IsFrostmanOn
      (coreShadingAwareCanonicalGlobalFrostmanConstant
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
      (coreShadingAwareSelectedStickyCover
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).activeCoarseFamily
      Finset.univ closedBallFourBody := by
  apply StickyScaleCover.activeCoarseFamily_isFrostmanOn_univ_canonical
    (coreShadingAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedActualDatum_isAdmissible
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (canonicalBufferedRadius_le_one
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
  exact (coreShadingAwareLogPartition
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
    ).coarseIndices_nonempty

/-- The canonical global constant is finite. -/
theorem coreShadingAwareCanonicalGlobalFrostmanConstant_ne_top
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    coreShadingAwareCanonicalGlobalFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass ≠ ∞ := by
  let S1 := coreShadingAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  have hglobal := coreShadingAwareCanonicalGlobalFrostman
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
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
      ((coreShadingAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).coarseIndices_nonempty)).ne'
  unfold coreShadingAwareCanonicalGlobalFrostmanConstant
  unfold canonicalFrostmanConstant
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top
      (maximalConcentration_lt_top S1.activeCoarseFamily).ne
      closedBallFourBody.isCompact.measure_lt_top.ne
  · exact hmass0

#print axioms coreShadingAwareSelectedActualDatum_isAdmissible
#print axioms coreShadingAwareCanonicalGlobalFrostmanConstant
#print axioms coreShadingAwareCanonicalGlobalFrostman
#print axioms coreShadingAwareCanonicalGlobalFrostmanConstant_ne_top

end
end Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1

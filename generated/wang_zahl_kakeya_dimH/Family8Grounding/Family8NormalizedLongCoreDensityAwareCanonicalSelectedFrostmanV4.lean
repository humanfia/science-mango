import Family8Grounding.Family8NormalizedLongCoreDensityAwareCanonicalGlobalFrostmanV2
import Family8Grounding.Family8NormalizedLongCoreDensityAwareCanonicalConflictChoiceV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
import Mathlib.Tactic

/-!
# Exact-degree selected Frostman data on the same long-core hierarchy, V4

The selected Frostman conclusion is stated explicitly as a theorem.  Its only
mass premise is nonzero mass of the already fixed exact-assembly refinement;
no body-mass selector is used as a substitute for shading-mass retention.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareCanonicalSelectedFrostmanV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreDensityAwareCanonicalConflictChoiceV1
open Family8NormalizedLongCoreDensityAwareCanonicalGlobalFrostmanV2
open Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2
open Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
open Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
open Family8ParameterLadderV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The selected-source loss used by the canonical buffered input. -/
noncomputable def coreDensityAwareCanonicalSelectedFrostmanConstant
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) : ENNReal :=
  coreDensityAwareCanonicalGlobalFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine *
    (16 * (Fintype.card
      (ActiveParentIndex
        (coreDensityAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)) : ENNReal))

/-- Finiteness survives the exact selected-source cardinality loss. -/
theorem coreDensityAwareCanonicalSelectedFrostmanConstant_ne_top
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    coreDensityAwareCanonicalSelectedFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine ≠ ∞ := by
  unfold coreDensityAwareCanonicalSelectedFrostmanConstant
  exact ENNReal.mul_ne_top
    (coreDensityAwareCanonicalGlobalFrostmanConstant_ne_top
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (by finiteness)

/-- Nonzero final refinement mass makes the exact-degree selected source
literally nonempty. -/
theorem coreDensityAwareCanonicalSelectedFine_nonempty
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hrefinementMass :
      (coreDensityAwareSelectedGreedyExactAssembly
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading.shadingMass ≠ 0) :
    (selectedOccurrenceFineIndices
      (actualUpperPartition
        (coreDensityAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
        (coreDensityAwareSelectedUpperIdentityCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
        (coreDensityAwareSelectedGreedyPartition
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine))
      (canonicalSelectedOccurrences
        (coreDensityAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
        (coreDensityAwareSelectedUpperIdentityCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
        (coreDensityAwareSelectedGreedyPartition
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
        (coreDensityAwareSelectedGreedyExactAssembly
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading)).Nonempty :=
  canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading
    hrefinementMass

/-- The exact selected-source Frostman theorem used by buffered `I`. -/
theorem coreDensityAwareCanonicalSelectedFrostman
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hrefinementMass :
      (coreDensityAwareSelectedGreedyExactAssembly
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading.shadingMass ≠ 0) :
    IsFrostmanOn
      (coreDensityAwareCanonicalSelectedFrostmanConstant
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
      (coreDensityAwareSelectedStickyCover
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).activeCoarseFamily
      (selectedOccurrenceFineIndices
        (actualUpperPartition
          (coreDensityAwareSelectedStickyCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
          (coreDensityAwareSelectedUpperIdentityCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
          (coreDensityAwareSelectedGreedyPartition
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine))
        (canonicalSelectedOccurrences
          (coreDensityAwareSelectedStickyCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
          (coreDensityAwareSelectedUpperIdentityCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
          (coreDensityAwareSelectedGreedyPartition
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
          (coreDensityAwareSelectedGreedyExactAssembly
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading))
      closedBallFourBody :=
  canonicalSelected_source_frostman_of_nonempty
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading
    closedBallFourBody
    (coreDensityAwareCanonicalGlobalFrostman
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareCanonicalSelectedFine_nonempty
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hrefinementMass)
    hrhoHalf

#print axioms coreDensityAwareCanonicalSelectedFrostmanConstant
#print axioms coreDensityAwareCanonicalSelectedFrostmanConstant_ne_top
#print axioms coreDensityAwareCanonicalSelectedFine_nonempty
#print axioms coreDensityAwareCanonicalSelectedFrostman

end
end Family8NormalizedLongCoreDensityAwareCanonicalSelectedFrostmanV4

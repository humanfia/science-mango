import Family8Grounding.Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1
import Family8Grounding.Family8NormalizedLongCoreShadingAwareCanonicalConflictChoiceV1
import Family8Grounding.Family8NormalizedLongCoreShadingAwareAssemblyMassPositiveV4
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
import Mathlib.Tactic

/-!
# Exact-degree selected Frostman data on the shading-aware long-core hierarchy

The exact assembly's positive mass is now a theorem of the shading-aware
selector, so the selected-source Frostman conclusion needs only the geometric
half-radius hypothesis and no mass callback.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareCanonicalSelectedFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareAssemblyMassPositiveV4
open Family8NormalizedLongCoreShadingAwareCanonicalConflictChoiceV1
open Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
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
set_option maxHeartbeats 3400000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Exact selected-source Frostman loss. -/
noncomputable def coreShadingAwareCanonicalSelectedFrostmanConstant
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
  coreShadingAwareCanonicalGlobalFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass *
    (16 * (Fintype.card
      (ActiveParentIndex
        (coreShadingAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)) :
            ENNReal))

theorem coreShadingAwareCanonicalSelectedFrostmanConstant_ne_top
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
    coreShadingAwareCanonicalSelectedFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass ≠ ∞ := by
  unfold coreShadingAwareCanonicalSelectedFrostmanConstant
  exact ENNReal.mul_ne_top
    (coreShadingAwareCanonicalGlobalFrostmanConstant_ne_top
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (by finiteness)

/-- The exact-degree selected fine source is nonempty, derived from actual
shading retention rather than assumed. -/
theorem coreShadingAwareCanonicalSelectedFine_nonempty
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
    (selectedOccurrenceFineIndices
      (actualUpperPartition
        (coreShadingAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
        (coreShadingAwareSelectedUpperIdentityCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
        (coreShadingAwareSelectedGreedyPartition
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass))
      (canonicalSelectedOccurrences
        (coreShadingAwareSelectedStickyCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
        (coreShadingAwareSelectedUpperIdentityCover
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
        (coreShadingAwareSelectedGreedyPartition
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
        (coreShadingAwareSelectedGreedyExactAssembly
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
          ).refinement.shading)).Nonempty :=
  canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
      ).refinement.shading
    (coreShadingAwareSelectedGreedyExactAssembly_refinementMass_ne_zero
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

/-- Canonical selected-source Frostman control. -/
theorem coreShadingAwareCanonicalSelectedFrostman
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
      D hD C Sseq P W hepsilonHalf ≠ 0)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹) :
    IsFrostmanOn
      (coreShadingAwareCanonicalSelectedFrostmanConstant
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
      (coreShadingAwareSelectedStickyCover
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).activeCoarseFamily
      (selectedOccurrenceFineIndices
        (actualUpperPartition
          (coreShadingAwareSelectedStickyCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          (coreShadingAwareSelectedUpperIdentityCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          (coreShadingAwareSelectedGreedyPartition
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass))
        (canonicalSelectedOccurrences
          (coreShadingAwareSelectedStickyCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          (coreShadingAwareSelectedUpperIdentityCover
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          (coreShadingAwareSelectedGreedyPartition
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          (coreShadingAwareSelectedGreedyExactAssembly
            D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
            ).refinement.shading))
      closedBallFourBody :=
  canonicalSelected_source_frostman_of_nonempty
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
      ).refinement.shading
    closedBallFourBody
    (coreShadingAwareCanonicalGlobalFrostman
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareCanonicalSelectedFine_nonempty
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    hrhoHalf

#print axioms coreShadingAwareCanonicalSelectedFrostmanConstant
#print axioms coreShadingAwareCanonicalSelectedFrostmanConstant_ne_top
#print axioms coreShadingAwareCanonicalSelectedFine_nonempty
#print axioms coreShadingAwareCanonicalSelectedFrostman

end
end Family8NormalizedLongCoreShadingAwareCanonicalSelectedFrostmanV1

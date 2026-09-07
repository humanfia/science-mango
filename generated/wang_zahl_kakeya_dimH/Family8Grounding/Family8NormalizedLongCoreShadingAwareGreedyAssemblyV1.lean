import Family8Grounding.Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
import Family8Grounding.Family8CanonicalFullGreedyExactAssemblyChoiceV3

/-!
# Greedy exact assembly on the shading-aware selected long-core hierarchy

The full greedy partition and exact assembly are run on the literal lower
cover selected by shading mass.  No sibling selection or transport equality
is used.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8CanonicalFullGreedyExactAssemblyChoiceV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The full greedy partition on the literal shading-aware selected cover. -/
noncomputable def coreShadingAwareSelectedGreedyPartition
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
      D hD C Sseq P W hepsilonHalf ≠ 0) :=
  canonicalFullGreedyPartition
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

/-- Parent-aggregate the unchanged actual source shading over precisely S1. -/
noncomputable def coreShadingAwareSelectedParentShading
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
      D hD C Sseq P W hepsilonHalf ≠ 0) :=
  parentAggregatedShading
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).shading

/-- The exact multiplicity assembly on the same `D1/S1/P1`. -/
noncomputable def coreShadingAwareSelectedGreedyExactAssembly
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
      D hD C Sseq P W hepsilonHalf ≠ 0) :=
  canonicalFullGreedyExactAssembly
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedParentShading
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

@[simp] theorem coreShadingAwareSelectedGreedyPartition_coveredIndices
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
    (coreShadingAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).coveredIndices =
      Finset.univ :=
  canonicalFullGreedyPartition_coveredIndices
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

#print axioms coreShadingAwareSelectedGreedyPartition
#print axioms coreShadingAwareSelectedParentShading
#print axioms coreShadingAwareSelectedGreedyExactAssembly
#print axioms coreShadingAwareSelectedGreedyPartition_coveredIndices

end
end Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1

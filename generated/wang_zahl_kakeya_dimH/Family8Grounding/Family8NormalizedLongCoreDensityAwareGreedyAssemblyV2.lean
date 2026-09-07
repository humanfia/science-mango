import Family8Grounding.Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
import Family8Grounding.Family8CanonicalFullGreedyExactAssemblyChoiceV3

/-!
# The same-object greedy assembly on a normalized long core, V2

This module specializes the two separately frozen canonical choices to the
density-aware selected datum and its literal lower sticky cover.  No sibling
selection or transport equality is used.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8CanonicalFullGreedyExactAssemblyChoiceV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
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
set_option maxHeartbeats 2400000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The full greedy partition run on the literal selected lower cover `S1`. -/
noncomputable def coreDensityAwareSelectedGreedyPartition
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  canonicalFullGreedyPartition
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)

/-- The actual parent-aggregated shading of the same selected datum `D1`. -/
noncomputable def coreDensityAwareSelectedParentShading
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  parentAggregatedShading
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedActualDatum
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).shading

/-- The exact multiplicity assembly on precisely the same `D1/S1/P1`. -/
noncomputable def coreDensityAwareSelectedGreedyExactAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  canonicalFullGreedyExactAssembly
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedParentShading
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)

@[simp] theorem coreDensityAwareSelectedGreedyPartition_coveredIndices
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (coreDensityAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).coveredIndices =
      Finset.univ :=
  canonicalFullGreedyPartition_coveredIndices
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)

#print axioms coreDensityAwareSelectedGreedyPartition
#print axioms coreDensityAwareSelectedParentShading
#print axioms coreDensityAwareSelectedGreedyExactAssembly
#print axioms coreDensityAwareSelectedGreedyPartition_coveredIndices

end
end Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2

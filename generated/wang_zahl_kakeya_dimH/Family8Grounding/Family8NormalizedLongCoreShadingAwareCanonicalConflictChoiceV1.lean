import Family8Grounding.Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2

/-!
# Canonical conflict choice on the shading-aware long-core hierarchy

The exact doubled-parent selection is run on the already frozen
`D1/S1/U1/P1/A1` objects and their literal assembly-refinement shading.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareCanonicalConflictChoiceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
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

/-- The literal doubled-parent conflict loss on `S1 -> U1`. -/
noncomputable def coreShadingAwareCanonicalConflictLoss
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
  canonicalEq45ConflictLoss
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

/-- The canonical exact-degree weighted conflict selection on the same
assembly-refinement shading. -/
noncomputable def coreShadingAwareCanonicalConflictSelection
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
  canonicalEq45ConflictSelection
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).refinement.shading

#print axioms coreShadingAwareCanonicalConflictLoss
#print axioms coreShadingAwareCanonicalConflictSelection

end
end Family8NormalizedLongCoreShadingAwareCanonicalConflictChoiceV1

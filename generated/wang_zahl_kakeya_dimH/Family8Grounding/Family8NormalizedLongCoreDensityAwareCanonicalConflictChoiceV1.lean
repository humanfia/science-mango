import Family8Grounding.Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2

/-!
# Canonical conflict choice on the same selected long-core hierarchy

The upper conflict selection is run on the already frozen `D1/S1/U1/P1/A1`
objects.  It is therefore definitionally the selection consumed by the
buffered Equation (45) input.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareCanonicalConflictChoiceV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2
open Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
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
set_option maxHeartbeats 2400000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The exact doubled-parent conflict loss on `S1 -> U1`. -/
noncomputable def coreDensityAwareCanonicalConflictLoss
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  canonicalEq45ConflictLoss
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)

/-- The canonical exact-degree weighted conflict selection on the same
assembly refinement shading. -/
noncomputable def coreDensityAwareCanonicalConflictSelection
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  canonicalEq45ConflictSelection
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading

#print axioms coreDensityAwareCanonicalConflictLoss
#print axioms coreDensityAwareCanonicalConflictSelection

end
end Family8NormalizedLongCoreDensityAwareCanonicalConflictChoiceV1

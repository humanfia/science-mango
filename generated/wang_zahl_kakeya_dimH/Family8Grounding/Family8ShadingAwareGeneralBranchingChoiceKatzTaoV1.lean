import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceV3

/-!
# Katz--Tao projection for the compact shading-aware choice
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ShadingAwareGeneralBranchingChoiceV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Retagging by the shading-aware bucket changes only refinement metadata,
so the compact chosen datum inherits every source Katz--Tao bound. -/
theorem coreShadingAwareGeneralBranchingChoice_isKatzTao
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT D.family.bodyFamily) :
    IsKatzTao KT
      (coreShadingAwareGeneralBranchingChoice
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).datum.family.bodyFamily := by
  rw [coreShadingAwareGeneralBranchingChoice]
  exact hKT

#print axioms coreShadingAwareGeneralBranchingChoice_isKatzTao

end
end Family8ShadingAwareGeneralBranchingChoiceKatzTaoV1

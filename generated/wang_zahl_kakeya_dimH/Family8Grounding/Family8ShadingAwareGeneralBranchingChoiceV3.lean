import Family8Grounding.Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1

/-!
# Compact chosen data for the shading-aware general-branching endpoint, V3

The proof-dependent canonical datum and partition are frozen behind one
small record.  Downstream scalar lemmas can use its fields without reducing
the full logarithmic selector and hierarchy construction.  V1 used Boolean
disequality and V2 tried to project an implicit coarse-family argument from
a partition; neither predecessor is imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareCanonicalGlobalFrostmanV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-- Minimal actual datum and literal coarse partition read by the discrete
general-branching scalar endpoint. -/
structure ShadingAwareGeneralBranchingChoice
    (delta b : NNReal) (index : Type) [Fintype index] [DecidableEq index] where
  datum : ActualTubeDatum delta index
  admissible : datum.IsAdmissible
  coarseCard : Nat
  coarse : UniformTubeFamily b (Fin coarseCard)
  partition : CoarseTubePartition datum.family coarse

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The compact choice attached to the one canonical shading-aware bucket.
Irreducibility prevents unrelated consumers from unfolding the selector. -/
irreducible_def coreShadingAwareGeneralBranchingChoice
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
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    ShadingAwareGeneralBranchingChoice
      delta (canonicalBufferedRadius W) index where
  datum := coreShadingAwareSelectedActualDatum
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  admissible := coreShadingAwareSelectedActualDatum_isAdmissible
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  coarseCard :=
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf).coarseCard
  coarse := (coreShadingAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).coarse
  partition := coreShadingAwareLogPartition
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass

#print axioms ShadingAwareGeneralBranchingChoice
#print axioms coreShadingAwareGeneralBranchingChoice

end
end Family8ShadingAwareGeneralBranchingChoiceV3

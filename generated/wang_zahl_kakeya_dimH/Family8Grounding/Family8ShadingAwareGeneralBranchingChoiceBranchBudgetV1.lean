import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceV3
import Family8Grounding.Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2

/-!
# Branch source-budget projection for the compact shading-aware choice
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceBranchBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ShadingAwareGeneralBranchingChoiceV3
open Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The efficient-parent branching budget, projected onto the compact
canonical choice. -/
theorem coreShadingAwareGeneralBranchingChoice_branchBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA longTarget : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hBranchAbsorb :
      524288 * stickyShadingAwareCoverLossNNReal
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
          D.shading sourceA * (2 : NNReal) ^ 2 <= longTarget) :
    8192 * ((coreShadingAwareGeneralBranchingChoice
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).partition.branchingLoss : NNReal) * sourceA *
          canonicalBufferedRadius W ^ 2 <=
      longTarget *
        ((coreShadingAwareGeneralBranchingChoice
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
          ).partition.branching : NNReal) * (delta ^ 2 / 2) := by
  rw [coreShadingAwareGeneralBranchingChoice]
  have hdeltaHalf : delta <= (2 : NNReal)⁻¹ :=
    (Sseq.delta_le_tau W.m).trans
      ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
        hrhoHalf)
  exact shadingAwareLogPartition_branch_sourceBudget
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    D.shading sourceA longTarget hsourceA
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by simpa only [coreShadingAwareActiveShadingMass] using hmass)
    hdeltaHalf hrhoHalf hBranchAbsorb

#print axioms coreShadingAwareGeneralBranchingChoice_branchBudget

end
end Family8ShadingAwareGeneralBranchingChoiceBranchBudgetV1

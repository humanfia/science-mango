import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceV3
import Family8Grounding.Family8StickyShadingAwareCanonicalLogFineSourceBudgetV1

/-!
# Fine source-budget projection for the compact shading-aware choice
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceFineBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ShadingAwareGeneralBranchingChoiceV3
open Family8StickyShadingAwareCanonicalLogFineSourceBudgetV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual shading-retention fine budget, projected onto the compact
canonical choice. -/
theorem coreShadingAwareGeneralBranchingChoice_fineBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA fineTarget : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hFineAbsorb :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (sourceA : ENNReal) <=
        (fineTarget : ENNReal) *
          coreShadingAwareActiveShadingMass
            D hD C Sseq P W hepsilonHalf) :
    8192 * ((coreShadingAwareGeneralBranchingChoice
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).partition.branchingLoss : NNReal) ^ 2 * sourceA <=
      fineTarget *
        ((coreShadingAwareGeneralBranchingChoice
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
          ).partition.fineIndices.card : NNReal) * (delta ^ 2 / 2) := by
  rw [coreShadingAwareGeneralBranchingChoice]
  have hdeltaHalf : delta <= (2 : NNReal)⁻¹ :=
    (Sseq.delta_le_tau W.m).trans
      ((tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le).trans
        hrhoHalf)
  exact shadingAwareLogPartition_fine_sourceBudget
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    D.shading sourceA fineTarget hsourceA
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by simpa only [coreShadingAwareActiveShadingMass] using hmass)
    hdeltaHalf hFineAbsorb

#print axioms coreShadingAwareGeneralBranchingChoice_fineBudget

end
end Family8ShadingAwareGeneralBranchingChoiceFineBudgetV1

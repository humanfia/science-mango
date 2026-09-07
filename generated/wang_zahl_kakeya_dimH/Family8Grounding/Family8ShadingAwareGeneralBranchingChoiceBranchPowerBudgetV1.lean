import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceBranchBudgetV1
import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1

/-!
# Branch power-envelope budget for the compact shading-aware choice
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceBranchPowerBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8LogarithmicSelectedScalarPowerBudgetsV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ShadingAwareGeneralBranchingChoiceBranchBudgetV1
open Family8ShadingAwareGeneralBranchingChoiceV3
open Family8StickyShadingAwareCanonicalLogBranchSourceBudgetV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta d : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- A power envelope for the honest shading-aware cover loss implies the
exact branching budget on the frozen canonical choice. -/
theorem coreShadingAwareGeneralBranchingChoice_branchBudget_of_powerEnvelope
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
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    {coverExponent absorbExponent longExponent : Real}
    (hd : 0 < d) (hdOne : d <= 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d <= branchingScalarThreshold absorbExponent)
    (hcover :
      (stickyShadingAwareCoverLossNNReal
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
          D.shading sourceA : ENNReal) <=
        (d : ENNReal) ^ (-coverExponent))
    (hexponent : coverExponent + absorbExponent <= longExponent) :
    8192 * ((coreShadingAwareGeneralBranchingChoice
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).partition.branchingLoss : NNReal) * sourceA *
          canonicalBufferedRadius W ^ 2 <=
      d ^ (-longExponent) *
        ((coreShadingAwareGeneralBranchingChoice
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
          ).partition.branching : NNReal) * (delta ^ 2 / 2) := by
  have hAbsorbENN := branching_scalarAbsorption_of_powerEnvelope
    hd hdOne habsorbExponent hdSmall hcover hexponent
  have hAbsorbNN :
      524288 * stickyShadingAwareCoverLossNNReal
          (canonicalBufferedGlobalCover
            W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
          D.shading sourceA * (2 : NNReal) ^ 2 <=
        d ^ (-longExponent) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_pow,
      ENNReal.coe_rpow_of_ne_zero hd.ne'] using hAbsorbENN
  exact coreShadingAwareGeneralBranchingChoice_branchBudget
    D hD C Sseq P W sourceA (d ^ (-longExponent)) hsourceA
      hepsilonHalf hfine hmass hrhoHalf hAbsorbNN

#print axioms
  coreShadingAwareGeneralBranchingChoice_branchBudget_of_powerEnvelope

end
end Family8ShadingAwareGeneralBranchingChoiceBranchPowerBudgetV1

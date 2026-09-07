import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceFineBudgetV1
import Family8Grounding.Family8LogarithmicSelectedScalarPowerBudgetsV1

/-!
# Fine power-envelope budget for the compact shading-aware choice
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceFinePowerBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8LogarithmicSelectedScalarPowerBudgetsV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ShadingAwareGeneralBranchingChoiceFineBudgetV1
open Family8ShadingAwareGeneralBranchingChoiceV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta d : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Paper-sized source coefficient and active-shading mass envelopes imply
the exact fine budget on the frozen canonical choice. -/
theorem coreShadingAwareGeneralBranchingChoice_fineBudget_of_powerEnvelopes
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
    {sourceExponent coefficientExponent absorbExponent baseExponent : Real}
    (hd : 0 < d) (hdOne : d <= 1)
    (habsorbExponent : 0 < absorbExponent)
    (hdSmall : d <= fineSourceScalarThreshold absorbExponent)
    (hcoefficient :
      ((2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) : ENNReal) *
          (sourceA : ENNReal) <=
        (d : ENNReal) ^ (-coefficientExponent))
    (hsourceMass : (d : ENNReal) ^ sourceExponent <=
      coreShadingAwareActiveShadingMass
        D hD C Sseq P W hepsilonHalf)
    (hexponent :
      sourceExponent + coefficientExponent + absorbExponent <=
        baseExponent) :
    8192 * ((coreShadingAwareGeneralBranchingChoice
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
        ).partition.branchingLoss : NNReal) ^ 2 * sourceA <=
      d ^ (-baseExponent) *
        ((coreShadingAwareGeneralBranchingChoice
          D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
          ).partition.fineIndices.card : NNReal) * (delta ^ 2 / 2) := by
  have hAbsorb := fineSource_scalarAbsorption_of_powerEnvelopes
    hd hdOne habsorbExponent hdSmall hcoefficient hsourceMass hexponent
  have hAbsorbNN :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (sourceA : ENNReal) <=
        ((d ^ (-baseExponent) : NNReal) : ENNReal) *
          coreShadingAwareActiveShadingMass
            D hD C Sseq P W hepsilonHalf := by
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using hAbsorb
  exact coreShadingAwareGeneralBranchingChoice_fineBudget
    D hD C Sseq P W sourceA (d ^ (-baseExponent)) hsourceA
      hepsilonHalf hfine hmass hrhoHalf hAbsorbNN

#print axioms
  coreShadingAwareGeneralBranchingChoice_fineBudget_of_powerEnvelopes

end
end Family8ShadingAwareGeneralBranchingChoiceFinePowerBudgetV1

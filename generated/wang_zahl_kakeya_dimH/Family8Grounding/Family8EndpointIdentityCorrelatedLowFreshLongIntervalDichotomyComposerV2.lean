import Family8Grounding.Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV2

/-!
# Correlated endpoint low-fresh terminal dichotomy composer, V2

The left branch is closed by the full-range V2 terminal under only
`gamma <= 1`.  The same-core high branch is transported by the identity
map, with its literal partition, selected prefix, occurrence, block, label,
and Cordoba witnesses unchanged.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV2
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LowFreshLongIntervalBaseScaleBridgeV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Close exactly the retained low branch of the correlated endpoint split
throughout the full range `gamma <= 1`.  The high implication is literally
the identity function. -/
theorem exists_endpointIdentity_correlated_dividingScaleOutput_or_sameCoreOccurrenceWeightedCordoba_massStrengthened_of_gamma_le_one
    {etaKT outputEta : Real} {delta0 : NNReal}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters
      beta (sectionEightFixedNu P) etaKT delta0)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (j : Nat) (hj : j <= P.N)
    (hbeta : 0 < beta)
    (hgammaOne : gamma <= 1)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hetaKTPos : 0 < etaKT)
    (hetaKTCap : etaKT <= P.epsilon ^ 2 * P.eta 0 / 32)
    (houtputCap : outputEta <= P.eta 0)
    (houtputShare : 16 * outputEta <= etaKT)
    (hdelta0 : delta / 8 <= delta0)
    (hsmallPower : delta <=
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
    (hsmallBase : delta <= lowFreshLongIntervalBaseScaleThreshold P)
    (hF : FrostmanHypotheses D outputEta)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover
        (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W).activeCoarseFamily) :
    EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
      D hD P W
        ((delta : ENNReal) ^ (-(etaKT / 8)))
        (DividingScaleOutput D P targetEpsilon)
        r hr KT := by
  let etaPrime : Real := 10 * P.eta j / (P.epsilon * beta)
  have hetaPrime0 : 0 <= etaPrime := by
    dsimp only [etaPrime]
    exact div_nonneg
      (mul_nonneg (by norm_num) (P.eta_pos j).le)
      (mul_nonneg P.epsilon_pos.le hbeta.le)
  have hsplit :=
    exists_endpointIdentity_correlated_retainedLowCardLower_or_sameCoreOccurrenceWeightedCordoba_massStrengthened
      (etaKT := etaKT) (outputEta := outputEta)
      (etaPrime := etaPrime) (delta0 := delta0)
      D hD P hKTP W hetaKTPos houtputShare hetaPrime0 hdelta0
        hsmallPower hF r hr KT hKT
  dsimp only at hsplit
  unfold
    EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
    at hsplit ⊢
  exact hsplit.imp
    (fun hretained =>
      endpointIdentity_retainedLowFresh_longInterval_dividingScaleOutput_of_gamma_le_one
        (etaKT := etaKT) (outputEta := outputEta)
        D hD P W j hj hbeta hgammaOne hTargetEpsilon0
          hetaKTPos hetaKTCap houtputCap houtputShare hF
          hsmallPower hsmallBase hretained)
    (fun hhigh => hhigh)

#print axioms
  exists_endpointIdentity_correlated_dividingScaleOutput_or_sameCoreOccurrenceWeightedCordoba_massStrengthened_of_gamma_le_one

end
end Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2

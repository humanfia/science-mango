import Family8Grounding.Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1
import Family8Grounding.Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV2
import Family8Grounding.Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
import Mathlib.Tactic

/-!
# Correlated endpoint dichotomy before the high occurrence is selected

This module runs the first-low greedy split directly on the endpoint
tau-active datum.  The low restriction is passed through the existing
correlated fresh selector and then to the retained-low terminal.  The high
branch stops at the literal greedy prefix: it retains the original partition,
selected prefix, factor-two mass, and pointwise high-occurrence cover, before
any occurrence or dyadic label is chosen.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCorrelatedPreQHighPrefixDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV2
open Family8EndpointIdentityTauActiveParentAdmissibilityV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV5
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LowFreshLongIntervalBaseScaleBridgeV1
open Family8LongIntervalBootstrapNumericsV1
open Family8MultiplicityLossMonotonicityV4
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Close the correlated retained-low branch throughout `gamma <= 1`, while
leaving the high branch at its literal pre-occurrence greedy prefix.

The high disjunct is returned directly by the core split on `Dtau`; no
occurrence, density bucket, side label, or container is selected here. -/
theorem exists_endpointIdentity_correlated_dividingScaleOutput_or_coreHighPrefixWithFirstHitMass_of_gamma_le_one
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
    (hF : FrostmanHypotheses D outputEta) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
    DividingScaleOutput D P targetEpsilon \/
      CoreHighPrefixWithFirstHitMass Dtau A := by
  dsimp only
  let etaPrime : Real := 10 * P.eta j / (P.epsilon * beta)
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
  have hetaPrime0 : 0 <= etaPrime := by
    dsimp only [etaPrime]
    exact div_nonneg
      (mul_nonneg (by norm_num) (P.eta_pos j).le)
      (mul_nonneg P.epsilon_pos.le hbeta.le)
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have hDtau : Dtau.IsAdmissible := by
    simpa only [E, C, S, T, Dtau] using
      (endpointIdentity_tauActiveParent_isAdmissible D hD P W)
  have hdensityEq :
      Dtau.shading.shadingDensity = D.shading.shadingDensity := by
    change (tauActiveCoarseDatum E C S W).shading.shadingDensity =
      D.shading.shadingDensity
    simpa only [E, C, S] using
      (endpointLongCore_identity_tauActive_shadingDensity_eq_source
        D hD P W)
  let B : LowFreshCorrelatedPowerBudgets
      delta etaKT outputEta (P.eta 0) A := by
    simpa only [A] using
      (lowFreshCorrelatedPowerBudgets_of_le_threshold
        P hD.delta_pos hetaKTPos houtputShare hsmallPower)
  have hKTPLong : KatzTaoAtParameters beta
      (longIntervalDeltaLoss P.epsilon etaPrime) etaKT delta0 :=
    katzTaoAtParameters_of_epsilon_le hKTP
      (sectionEightFixedNu_le_longIntervalDeltaLoss P hetaPrime0)
  rcases
      exists_factorTwo_lowKatzTaoRestriction_or_coreHighPrefixWithFirstHitMass
        Dtau A with hlow | hhigh
  · obtain ⟨selected, hmassTau, hlocalKT⟩ := hlow
    have hDlow :
        (restrictActualTubeDatum Dtau selected).IsAdmissible :=
      Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hDtau selected
    have hdelta0Tau : S.tau W.m / 8 <= delta0 := by
      simpa only [htau] using hdelta0
    have hdensityBudgetTau :
        (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
            (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
          Dtau.shading.shadingDensity := by
      have hdensityBudgetSource :
          (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
              (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
            D.shading.shadingDensity := by
        simpa only [htau] using B.density_budget.trans hF.1
      exact hdensityBudgetSource.trans_eq hdensityEq.symm
    have hcoefficientTau :
        128 * A <=
          ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT) := by
      simpa only [htau] using B.coefficient_budget
    have hretained :
        RetainedFactorTwoFreshLowWithCardLower Dtau A
          (longIntervalDeltaLoss P.epsilon etaPrime) beta :=
      retainedFactorTwoFreshLowWithCardLower_of_lowRestriction
        hKTPLong Dtau selected hmassTau hDlow A hlocalKT
          hdelta0Tau hdensityBudgetTau hcoefficientTau
    exact Or.inl
      (endpointIdentity_retainedLowFresh_longInterval_dividingScaleOutput_of_gamma_le_one
        (etaKT := etaKT) (outputEta := outputEta)
        D hD P W j hj hbeta hgammaOne hTargetEpsilon0
          hetaKTPos hetaKTCap houtputCap houtputShare hF
          hsmallPower hsmallBase
          (by simpa only [etaPrime, E, C, S, T, Dtau, A] using hretained))
  · exact Or.inr (by
      simpa only [E, C, S, T, Dtau, A] using hhigh)

#print axioms
  exists_endpointIdentity_correlated_dividingScaleOutput_or_coreHighPrefixWithFirstHitMass_of_gamma_le_one

end
end Family8EndpointIdentityCorrelatedPreQHighPrefixDichotomyV1

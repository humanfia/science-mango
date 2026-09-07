import Family8Grounding.Family8EndpointIdentityCorrelatedLowCardLowerMassStrengthenedV1
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8LongIntervalKatzTaoCountNormalizationV2
import Family8Grounding.Family8LowFreshCardScaleParameterLadderBudgetV1
import Family8Grounding.Family8LowFreshDSOOuterLossLedgerV1
import Family8Grounding.Family8LowFreshLongIntervalBaseScaleBridgeV1
import Family8Grounding.Family8LowFreshLongIntervalTargetActualDSOTransportV1
import Family8Grounding.Family8LowFreshLongIntervalXBoundsV1
import Mathlib.Tactic

/-!
# Endpoint low-fresh long-interval terminal composer

This file consumes one already selected low restriction and its one already
selected fresh child.  It does not invoke either selector again.  The retained
average is normalized with the card-scale bounds for that same fresh child,
passed through the long-interval numerical estimate, and finally transported
to the actual-volume right branch of `DividingScaleOutput`.

The conclusion is exactly the existing DSO proposition.  In particular no
stronger loss, stage, or volume conclusion is introduced here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8LongIntervalKatzTaoCountNormalizationV2
open Family8LowFreshCardScaleParameterLadderBudgetV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LowFreshDSOOuterLossLedgerV1
open Family8LowFreshLongIntervalBaseScaleBridgeV1
open Family8LowFreshLongIntervalTargetActualDSOTransportV1
open Family8LowFreshLongIntervalXBoundsV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Close the low-fresh endpoint branch on its literal retained objects.

The two small-scale premises have disjoint jobs: `hsmallPower` constructs the
coefficient/fresh-loss budgets already used by the selector, while
`hsmallBase` supplies the sole scale comparison required by the numerical
long-interval consumer.  Neither premise makes a second geometric choice. -/
theorem endpointIdentity_retainedLowFresh_longInterval_dividingScaleOutput
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (j : Nat) (hj : j <= P.N)
    {etaKT outputEta : Real}
    (hbeta : 0 < beta)
    (hlowGamma : gamma <= (2 : Real) / 3)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hetaKTPos : 0 < etaKT)
    (hetaKTCap : etaKT <= P.epsilon ^ 2 * P.eta 0 / 32)
    (houtputCap : outputEta <= P.eta 0)
    (houtputShare : 16 * outputEta <= etaKT)
    (hF : FrostmanHypotheses D outputEta)
    (hsmallPower : delta <=
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
    (hsmallBase : delta <= lowFreshLongIntervalBaseScaleThreshold P)
    (hretained :
      let etaPrime := 10 * P.eta j / (P.epsilon * beta)
      let E := fullRefinementDatum D
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let T := tauScaleCover E C S W
      let Dtau := activeParentActualTubeDatum T E.shading
      let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
      RetainedFactorTwoFreshLowWithCardLower Dtau A
        (longIntervalDeltaLoss P.epsilon etaPrime) beta) :
    DividingScaleOutput D P targetEpsilon := by
  let etaPrime : Real := 10 * P.eta j / (P.epsilon * beta)
  let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
  let B : LowFreshCorrelatedPowerBudgets
      delta etaKT outputEta (P.eta 0) A := by
    simpa only [A] using
      (lowFreshCorrelatedPowerBudgets_of_le_threshold
        P hD.delta_pos hetaKTPos houtputShare hsmallPower)
  have hgammaOne : gamma <= 1 := by
    linarith
  have hgammaTwo : gamma <= 2 := by
    linarith
  have hetaStagePrime : P.eta j <= etaPrime := by
    dsimp only [etaPrime]
    exact parameterLadder_eta_le_longIntervalEtaPrime
      P j hbeta hgammaOne
  have hetaPrime0 : 0 <= etaPrime :=
    (P.eta_pos j).le.trans hetaStagePrime
  have hexponent :
      2 * outputEta + (etaKT / 2 + P.eta 0) + P.eta 0 <=
        etaPrime := by
    dsimp only [etaPrime]
    simpa only [add_assoc] using
      (lowGate_freshCardScale_exponent_budget
        P j hj hbeta hlowGamma houtputCap hetaKTCap)
  have hepsilonOne : P.epsilon <= 1 := by
    nlinarith [P.epsilon_gap, hlowGamma, hbeta]
  have hepsilonSqOne : P.epsilon ^ 2 <= 1 := by
    have hproduct : 0 <= P.epsilon * (1 - P.epsilon) :=
      mul_nonneg P.epsilon_pos.le (sub_nonneg.mpr hepsilonOne)
    nlinarith
  have hetaKTLeEtaZero : etaKT <= P.eta 0 := by
    have hscaled : P.epsilon ^ 2 * P.eta 0 <= P.eta 0 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hepsilonSqOne (P.eta_pos 0).le
    have hscaled0 : 0 <= P.epsilon ^ 2 * P.eta 0 :=
      mul_nonneg (sq_nonneg _) (P.eta_pos 0).le
    have hdiv : P.epsilon ^ 2 * P.eta 0 / 32 <=
        P.epsilon ^ 2 * P.eta 0 := by
      nlinarith
    exact hetaKTCap.trans (hdiv.trans hscaled)
  have hetaLoss :
      etaKT <= longIntervalDeltaLoss P.epsilon etaPrime := by
    have hetaZeroStage : P.eta 0 <= P.eta j :=
      eta_zero_le_eta_of_stage_le P j hj
    dsimp only [longIntervalDeltaLoss]
    linarith [hetaKTLeEtaZero, hetaZeroStage, hetaStagePrime,
      P.epsilon_pos]
  have hbase : delta <= (delta / 8) ^ (1 - P.epsilon) :=
    delta_le_eighth_rpow_one_sub_of_le_threshold
      P hD.delta_pos hsmallBase
  have hd : 0 < delta / 8 :=
    div_pos hD.delta_pos (by norm_num)
  have hdb : delta / 8 <= delta :=
    div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)
  have hdOne : delta / 8 <= 1 :=
    hdb.trans (hD.delta_le_half.trans (by norm_num))
  dsimp only at hretained
  unfold RetainedFactorTwoFreshLowWithCardLower at hretained
  obtain ⟨selectedLow, hmass, hDlow, hKTlow,
      selectedFresh, hselectedFresh, hcardUpper, hcardLower,
      _hnormalizedMass, haverage⟩ := hretained
  have hX : LowFreshLongIntervalXBounds
      delta selectedFresh.card P.epsilon etaPrime := by
    exact endpointIdentity_tauActive_lowFresh_longIntervalXBounds
      D hD P W hF A
        (etaKT := etaKT)
        (lossExponent := etaKT / 2 + P.eta 0)
        (absorbExponent := P.eta 0)
        (etaPrime := etaPrime)
        B.coefficient_budget B.fresh_loss_budget B.sixteen_budget
        hexponent hetaPrime0 hetaLoss
        selectedLow hmass hDlow hKTlow selectedFresh hselectedFresh
        hcardUpper hcardLower
  have hnormalizedTarget :
      katzTaoMultiplicityRHS (delta / 8) selectedFresh.card
          (longIntervalDeltaLoss P.epsilon etaPrime) beta <=
        longIntervalFrostmanTargetENNReal (delta / 8) delta
          (lowFreshLongIntervalX delta selectedFresh.card)
          etaPrime gamma := by
    dsimp only [etaPrime]
    exact katzTaoMultiplicityRHS_le_longIntervalFrostmanTargetENNReal
      P j hd hdOne hdb hbase
        (show lowFreshLongIntervalX delta selectedFresh.card =
          (selectedFresh.card : NNReal) * delta ^ 2 by rfl)
        hX.lower hX.upper (Finset.card_pos.mpr hselectedFresh)
        hbeta hgammaOne
  have hsourceTarget :
      D.shading.averageMultiplicity <=
        (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          longIntervalFrostmanTargetENNReal (delta / 8) delta
            ((selectedFresh.card : NNReal) * delta ^ 2)
            etaPrime gamma := by
    calc
      D.shading.averageMultiplicity <=
          (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
            katzTaoMultiplicityRHS (delta / 8) selectedFresh.card
              (longIntervalDeltaLoss P.epsilon etaPrime) beta := by
        rw [<- endpointLongCore_tauActive_averageMultiplicity_eq_source
          D hD P W]
        exact haverage
      _ <= (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          longIntervalFrostmanTargetENNReal (delta / 8) delta
            (lowFreshLongIntervalX delta selectedFresh.card)
            etaPrime gamma :=
        mul_le_mul' le_rfl hnormalizedTarget
      _ = (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          longIntervalFrostmanTargetENNReal (delta / 8) delta
            ((selectedFresh.card : NNReal) * delta ^ 2)
            etaPrime gamma := by
        rfl
  have houter :
      ((2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          (2 : ENNReal) ^ (1 - gamma / 2)) <=
        (delta : ENNReal) ^ (-3 * P.eta j) := by
    exact lowFreshCorrelatedPowerBudgets_native_outerLoss
      P j hj hD.delta_pos hbeta.le hgammaOne hetaKTCap B
  exact endpointIdentity_lowFreshTarget_dividingScaleOutput
    D hD P W j hj (etaPrime := etaPrime)
      hetaStagePrime hTargetEpsilon0 hgammaTwo
      selectedLow selectedFresh
      (2 * (sourceKatzTaoFreshLoss A : ENNReal))
      hsourceTarget houter

#print axioms
  endpointIdentity_retainedLowFresh_longInterval_dividingScaleOutput

end
end Family8EndpointIdentityLowFreshLongIntervalTerminalComposerV1

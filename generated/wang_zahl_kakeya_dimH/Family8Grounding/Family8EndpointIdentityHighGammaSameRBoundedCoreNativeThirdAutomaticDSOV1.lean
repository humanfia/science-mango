import Family8Grounding.Family8CanonicalGraphFrozenEndpointIdentityLossFreeTripleV1
import Family8Grounding.Family8EndpointFirstCrossingIdentityFrozenLossPowerV3
import Family8Grounding.Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdBoundedDSOV1
import Family8Grounding.Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1
import Family8Grounding.Family8EndpointIdentityHighGammaSameGraphLossFourPowerV1
import Family8Grounding.Family8EndpointLongCoreThirdLossPowerV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Mathlib.Tactic

/-!
# Automatic endpoint same-R bounded Core-native-third DSO

This adapter connects the literal bounded factorization used by the
gamma-native third-first producer to the graph-loss-free three-scale
consumer.  The raw product is supplied by the endpoint singleton-fibre
theorem on the same `R`; no graph loss, exact outer field, proxy, or graph
reselection occurs.

The frozen assembly loss and the fixed coefficient four are paid by the
existing endpoint small-scale threshold.  The literal gamma-native third
loss is paid by its existing fixed-conflict power theorem.  Consequently the
only new scalar allocation is the displayed third-exponent budget.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaSameRBoundedCoreNativeThirdAutomaticDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalGraphFrozenEndpointIdentityLossFreeTripleV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointFirstCrossingIdentityFrozenLossPowerV3
open Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdBoundedDSOV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1
open Family8EndpointIdentityHighGammaSameGraphLossFourPowerV1
open Family8EndpointLongCoreThirdLossPowerV1
open Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Half of the strict high-gamma reserve left after the ten-eta payment. -/
def sameRHighGammaMiddleLossExponent
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : Real :=
  (P.epsilon ^ 2 * (3 * gamma - 2) - 10 * P.eta stage) / 2

theorem sameRHighGammaMiddleLossExponent_pos
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat)
    (hHigh : 10 * P.eta stage < P.epsilon ^ 2 * (3 * gamma - 2)) :
    0 < sameRHighGammaMiddleLossExponent P stage := by
  unfold sameRHighGammaMiddleLossExponent
  linarith

/-- The exact endpoint frozen loss carried by the gamma-native graph
assembly satisfies the high-gamma singleton middle estimate. -/
theorem endpointIdentity_highGamma_frozenLossFour_le_middle
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hGammaOne : gamma <= 1)
    (hHigh : 10 * P.eta W.stage < P.epsilon ^ 2 * (3 * gamma - 2))
    (assemblyLoss : Nat)
    (hAssemblyLoss :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let U := activeFineRestrictedScaleCover U0
      assemblyLoss = frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U.coarseCard))
    (hsmallMiddle : delta <=
      endpointFirstCrossingFrozenLossFourThreshold
        (sameRHighGammaMiddleLossExponent P W.stage)) :
    (assemblyLoss : ENNReal) * 4 <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) 1 gamma := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let lossExp := sameRHighGammaMiddleLossExponent P W.stage
  have hlossExp : 0 < lossExp := by
    simpa only [lossExp] using
      sameRHighGammaMiddleLossExponent_pos P W.stage hHigh
  have hhalf : 0 < lossExp / 2 := div_pos hlossExp (by norm_num)
  have hLossRaw := canonicalBufferedTauActive_frozenLoss_le_power
    E hE C S P W hepsilonHalf hhalf
      (hsmallMiddle.trans (min_le_left _ _))
  have hLoss : (assemblyLoss : ENNReal) <=
      (delta : ENNReal) ^ (-(lossExp / 2)) := by
    rw [hAssemblyLoss]
    change (frozenComparableLoss {i // i ∈ U0.activeFine}
      (Fin U.coarseCard) : ENNReal) <=
        (delta : ENNReal) ^ (-(lossExp / 2))
    have hcoarseCard : U.coarseCard = U0.activeCoarse.card := rfl
    rw [hcoarseCard]
    exact hLossRaw
  have hFour : (4 : ENNReal) <=
      (delta : ENNReal) ^ (-(lossExp / 2)) := by
    exact FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1.finiteConstant_le_delta_negativePower
      (K := (4 : ENNReal)) (by norm_num) hhalf hD.delta_pos
        (hsmallMiddle.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have houter : (assemblyLoss : ENNReal) * 4 <=
      (delta : ENNReal) ^ (-lossExp) := by
    calc
      (assemblyLoss : ENNReal) * 4 <=
          (delta : ENNReal) ^ (-(lossExp / 2)) *
            (delta : ENNReal) ^ (-(lossExp / 2)) :=
        mul_le_mul' hLoss hFour
      _ = (delta : ENNReal) ^ (-lossExp) := by
        rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1
        ring
  let rho := canonicalBufferedRadius W
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hgammaTwo : gamma <= 2 := hGammaOne.trans (by norm_num)
  obtain ⟨_q0, _qTop, hqPower⟩ :=
    canonicalBufferedTauActive_ratio_power_inputs E hE C S P W
  have hratio : (S.tau W.m : ENNReal) / (rho : ENNReal) <=
      (delta : ENNReal) ^ (P.epsilon ^ 2) := by
    simpa only [rho, ENNReal.coe_div hrho.ne'] using hqPower
  have hgain : 0 < 3 * gamma - 2 := by
    have hepsilonSq : 0 < P.epsilon ^ 2 := sq_pos_of_pos P.epsilon_pos
    have heta : 0 < 10 * P.eta W.stage :=
      mul_pos (by norm_num) (P.eta_pos W.stage)
    nlinarith
  have hbudget :
      10 * P.eta W.stage + lossExp <=
        P.epsilon ^ 2 * (3 * gamma - 2) := by
    dsimp only [lossExp, sameRHighGammaMiddleLossExponent]
    linarith
  simpa only [S, rho] using
    (sourceLoss_four_le_globalPower_mul_sectionEight_singleton
      hD.delta_pos hdeltaOne htau hrho hgammaTwo hgain hratio houter hbudget)

/-- Close the endpoint DSO on the exact bounded factorization, graph
assembly, and gamma-native third bundle.  Besides standard positivity and
small-scale hypotheses already used by the producer, the only scalar
allocation exposed here is `hThirdExponent`.
-/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_sameR_bounded_coreNativeThird
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hGammaOne : gamma <= 1)
    (hHigh : 10 * P.eta W.stage < P.epsilon ^ 2 * (3 * gamma - 2))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    {CKT : ENNReal}
    {etaKT conflictAbsorb thirdAbsorb epsilonThird : Real}
    (hetaKT : 0 <= etaKT)
    (hCKTfinite : CKT ≠ ∞) (hCKTone : 1 <= CKT)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hconflictAbsorb : 0 < conflictAbsorb)
    (hthirdAbsorb : 0 < thirdAbsorb)
    (hepsilonThird : 0 <= epsilonThird)
    (hsmallMiddle : delta <=
      endpointFirstCrossingFrozenLossFourThreshold
        (sameRHighGammaMiddleLossExponent P W.stage))
    (hsmallThird : delta <=
      endpointLongCoreThirdLossSmallDeltaThreshold
        conflictAbsorb thirdAbsorb epsilonThird gamma)
    (hThirdExponent :
      (etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb <=
        3 * P.eta W.stage) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    forall (M : Nat)
      (hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M)
      (hcoarse : U.activeCoarse.Nonempty),
      let Pcoarse := boundedFiberCoarseTubePartition U
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
        hcoarse M hM
      forall (fibreCF thirdLoss : ENNReal)
        (R : SameAssemblyFullCoefficientGraphIdentity
          (activeFineRestrictedFamily U0) U
          Pcoarse.asConvexFactorization Y fibreCF),
        R.A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
        thirdLoss = eighthSelectedThirdFactorLoss
          (canonicalBufferedRadius W)
          ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal)
          epsilonThird gamma ->
        forall _X : CoreNativeFrozenThirdBundle
          Pcoarse.asConvexFactorization Y R.A
          (canonicalBufferedRadius W) thirdLoss gamma,
          DividingScaleOutput D P targetEpsilon := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  intro M hM hcoarse
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse M hM
  intro fibreCF thirdLoss R hAloss hthirdLoss X
  have hMiddle : (R.A.loss : ENNReal) * 4 <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) (canonicalBufferedRadius W) 1 gamma :=
    endpointIdentity_highGamma_frozenLossFour_le_middle
      D hD P W hepsilonHalf hGammaOne hHigh R.A.loss hAloss hsmallMiddle
  have hThirdBase : X.thirdLoss <=
      (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb)) := by
    change thirdLoss <=
      (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb))
    calc
      thirdLoss = eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
          ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
            ENNReal) epsilonThird gamma := hthirdLoss
      _ <= (delta : ENNReal) ^
          (-((etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb)) :=
        canonicalBuffered_fixedConflict_thirdLoss_le_power
          (thirdBeta := gamma) E hE C S P W hetaKT hCKTfinite hCKTone hCKT
            hconflictAbsorb hthirdAbsorb hepsilonThird hsmallThird
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have hPower : (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + epsilonThird + thirdAbsorb)) <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne (by linarith)
  have hThirdPower : X.thirdLoss <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage) :=
    hThirdBase.trans hPower
  exact
    dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_bounded_coreNativeThird
      D hD P W hepsilonHalf hSmall hTargetEpsilon hGammaOne
        M hM hcoarse fibreCF thirdLoss
        R X hMiddle hThirdPower

#print axioms endpointIdentity_highGamma_frozenLossFour_le_middle
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_sameR_bounded_coreNativeThird

end
end Family8EndpointIdentityHighGammaSameRBoundedCoreNativeThirdAutomaticDSOV1

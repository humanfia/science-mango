import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointIdentitySelectedFineSingletonFrostmanV3
import Family8Grounding.Family8EndpointIdentitySingletonAssemblySelectedFineDirectCardPowerV2
import Family8Grounding.Family8EndpointIdentitySourceActiveFineDensityFloorV2
import Family8Grounding.Family8IdentityMassPopularContractedScaleBudgetV4
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8IdentityMassPopularNoKTConstantPowersV3
import Family8Grounding.Family8NoKTMiddleCallInputsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Endpoint identity inputs for the no-KT long-middle call

This module performs the endpoint object setup and all ratio, density, base,
card, and fibre-Frostman calculations.  It deliberately stops at the packaged
generic call inputs, so the actual fresh-middle invocation is a separate small
declaration.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityNoKTMiddleCallInputsV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8AllFrostmanStickyUnionProducerV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8EndpointIdentitySelectedFineSingletonFrostmanV3
open Family8EndpointIdentitySingletonAssemblySelectedFineDirectCardPowerV2
open Family8EndpointIdentitySourceActiveFineDensityFloorV2
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentityMassPopularContractedScaleBudgetV4
open Family8IdentityMassPopularNoKTConstantPowersV3
open Family8IdentityMassPopularNoKTPowerEnvelopeV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NoKTMiddleCallInputsV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The literal endpoint singleton assembly supplies every dependent input of
the generic no-KT middle producer.  No fresh-middle selection is performed in
this theorem. -/
theorem endpointLongCore_identity_noKT_callInputs
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {etaSource frostmanEta : Real}
    (hFsource : FrostmanHypotheses D etaSource)
    {lowerExp cardExp a cardAbsorbExp kappa : Real}
    (hcardExp : 0 ≤ cardExp) (hcountExp : 0 < 2 + kappa)
    {lossExp densityAbsorbExp baseAbsorbExp : Real}
    (hlossExp : 0 < lossExp)
    (hdensityAbsorbExp : 0 < densityAbsorbExp)
    (hbaseAbsorbExp : 0 < baseAbsorbExp)
    (hsmallLoss : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossExp)
    (hsmallDensityConstant : delta ≤
      identityMassPopularDensityPowerThreshold densityAbsorbExp)
    (hsmallBaseConstant : delta ≤
      identityMassPopularBasePowerThreshold frostmanEta
        (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) a
        baseAbsorbExp)
    (hdensityGain : 0 ≤ frostmanEta -
      ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))
    (hdensityExponentBudget :
      etaSource + lossExp + densityAbsorbExp ≤
        P.epsilon ^ 2 *
          (frostmanEta -
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)))
    (hbaseGain : 0 ≤ frostmanEta -
      (2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a) - 2)
    (hbaseExponentBudget :
      etaSource + lossExp + baseAbsorbExp ≤
        P.epsilon ^ 2 *
          (frostmanEta -
            (2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a) - 2)) :
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
    let tau := S.tau W.m
    let rho := canonicalBufferedRadius W
    let htauRho : tau ≤ rho :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 := by
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        have hfloor :=
          delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFsource
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
      rw [shadingMass_restrictTo_eq_sum]
      exact hOn
    let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U htauRho hcoarse 1 hM
    ∀ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) →
      CallInputs U Y 1 htauRho hcoarse hM A
        frostmanEta lowerExp cardExp a cardAbsorbExp kappa
        (sourceActiveFineShading
          (toConvexFactorization U) Y).shadingDensity
        (capturedTubeBoxLoss tau rho) 1 := by
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
  let tau := S.tau W.m
  let rho := canonicalBufferedRadius W
  let qratio : ENNReal := (tau : ENNReal) / (rho : ENNReal)
  let p : Real := 2 * lowerExp + 2 * cardExp + a + cardAbsorbExp
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have htauRho : tau ≤ rho := by
    dsimp only [tau, rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hFsource
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  have hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U htauRho hcoarse 1 hM
  intro A hAloss
  obtain ⟨hq0, hqTop, hqPower⟩ :=
    canonicalBufferedTauActive_ratio_power_inputs E hE C S P W
  have hLossRaw := canonicalBufferedTauActive_frozenLoss_le_power
    E hE C S P W hepsilonHalf hlossExp hsmallLoss
  have hLossPower : (A.loss : ENNReal) ≤
      (delta : ENNReal) ^ (-lossExp) := by
    rw [hAloss]
    change (frozenComparableLoss {i // i ∈ U0.activeFine}
      (Fin U.coarseCard) : ENNReal) ≤ (delta : ENNReal) ^ (-lossExp)
    have hcoarseCard : U.coarseCard = U0.activeCoarse.card := rfl
    rw [hcoarseCard]
    exact hLossRaw
  have hdensityFloor : (delta : ENNReal) ^ etaSource ≤
      (sourceActiveFineShading
        (toConvexFactorization U) Y).shadingDensity := by
    simpa only [E, hE, C, S, U0, Dtau, U, Y] using
      endpointLongCore_identity_sourceActiveFineShading_density_lower
        D hD P W hepsilonHalf hFsource
  have hdensityConstant :=
    identityMassPopularDensityFixedConstant_le_power
      hdensityAbsorbExp hD.delta_pos hsmallDensityConstant
  have hbaseConstant :=
    identityMassPopularBaseFixedConstant_le_power
      hbaseAbsorbExp hD.delta_pos hsmallBaseConstant
  have hdensityEnvelope := densityEnvelope_of_powerCaps_noKT
    hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hLossPower
      hdensityConstant hqPower hdensityGain hdensityExponentBudget
        hdensityFloor
  have hbaseEnvelope := baseEnvelope_of_powerCaps_noKT
    hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hLossPower
      hbaseConstant hqPower hbaseGain hbaseExponentBudget hdensityFloor
  have hdensityBudgetRaw :=
    contractedScale_densityBudget_of_ratioEnvelope
      hdensityGain hdensityEnvelope
  have hbaseBudgetRaw :=
    contractedScale_baseBudget_of_ratioEnvelope hq0 hqTop hbaseEnvelope
  have hproxyEqNN : contractedJohnProxyRadius tau rho / 8 =
      (3 / 64 : NNReal) * (tau / rho) :=
    contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho
  have hproxyEq :
      ((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) =
        (3 / 64 : ENNReal) * qratio := by
    rw [hproxyEqNN]
    push_cast
    rw [ENNReal.coe_div (by norm_num : (64 : NNReal) ≠ 0),
      ENNReal.coe_div hrho.ne']
    rfl
  have hdensityBudget :
      16 * (A.loss : ENNReal) *
          (((((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
              (frostmanEta - (p + a))) * 93312) * 128) ≤
        (sourceActiveFineShading
          (toConvexFactorization U) Y).shadingDensity := by
    simpa only [p, qratio, tau, rho, hproxyEq] using hdensityBudgetRaw
  have hbaseBudget :
      16 * (A.loss : ENNReal) *
          (((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
            (-(2 * p + a))) ≤
        (((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
            (-frostmanEta)) *
          ((((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
            (2 : Nat)) / 2) *
          (sourceActiveFineShading
            (toConvexFactorization U) Y).shadingDensity := by
    simpa only [p, qratio, tau, rho, hproxyEq] using hbaseBudgetRaw
  have hcards :=
    endpointLongCore_identity_singletonAssembly_selectedFine_directDualCardPower
      D hD P W hepsilonHalf hFsource hcardExp hcountExp A
  let hindices := assembly_indices_subset_activeFine U Y 1 A
  let T := selectedFineScaleCover U A.refinement.indices hindices
  have hcardAndCount : ∀ q : {q // q ∈ T.activeCoarse},
      (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          (((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
            (-cardExp)) ∧
        (Fintype.card {i // i ∈ T.fiber q.1} : ENNReal) ≤
          1 * (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
    simpa only [E, hE, C, S, U0, Dtau, U, Y, hsource, hM, hcoarse,
      Pcoarse, tau, rho, hindices, T] using hcards
  have hLowEvery : ∀ q : {q // q ∈ T.activeCoarse},
      IsFrostmanIn (capturedTubeBoxLoss tau rho)
        (T.fiberFamily q.1) (T.activeCoarseFamily q) := by
    intro q
    simpa only [T, hindices, U, U0, tau, rho] using
      identityCore_selectedFineTauActive_fiber_isFrostmanIn
        E hE S W P.epsilon_pos.le hepsilonHalf
          A.refinement.indices hindices q
  have hlowerTop : capturedTubeBoxLoss tau rho ≠ ∞ := by
    unfold capturedTubeBoxLoss
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
        ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  exact {
    hsource := hsource
    hlowerTop := hlowerTop
    hLowEvery := by simpa only [T, hindices] using hLowEvery
    hdensityFloor := le_rfl
    hdensityBudget := by simpa only [p] using hdensityBudget
    hbaseBudget := by simpa only [p] using hbaseBudget
    hcardAndCount := by simpa only [T, hindices] using hcardAndCount }

#print axioms endpointLongCore_identity_noKT_callInputs

end
end Family8EndpointIdentityNoKTMiddleCallInputsV7

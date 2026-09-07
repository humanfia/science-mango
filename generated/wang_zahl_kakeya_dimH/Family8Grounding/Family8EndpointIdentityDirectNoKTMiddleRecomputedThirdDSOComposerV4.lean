import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8EndpointIdentityExactOuterRecomputedThirdV6
import Family8Grounding.Family8EndpointIdentityNoKTMiddleCallInputsV7
import Family8Grounding.Family8EndpointLongCoreIdentityIntervalCountsV3
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
import Family8Grounding.Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
import Family8Grounding.Family8FirstCrossingActiveIndexThirdBetaGammaRefoldV4
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Family8Grounding.Family8NoKTMiddleCallInputsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import FamilyStickyGrounding.FamilyStickyCapturedTubeBoxWidthCleanV2
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Direct endpoint no-KT middle plus recomputed-third LongCore composer, canonical-loss G1

This endpoint chooses the literal singleton exact-outer assembly once.  It
passes the validated `CallInputs` builder directly to the generic no-KT
runner, constructs the recomputed third bundle on that same assembly, and
feeds the selected witness to the validated LongCore DSO connector.

The genuinely unresolved numerical work remains explicit: the two
recomputed-third gates, the beta-to-gamma card-scale gate, the extra outer
loss absorption for the middle factor, and the final third-loss power.

Unlike V3, the density gate is asked only for assemblies whose loss is the
canonical frozen-comparable loss.  The endpoint producer supplies that
equality for the actual selected assembly; no numerical density budget is
claimed here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityDirectNoKTMiddleRecomputedThirdDSOComposerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalEndpointBaseThresholdV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnMiddleFourGlobalPowerAbsorptionV2
open Family8ContractedJohnMiddleRelativeScaleEnvelopeV3
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityExactOuterRecomputedThirdV6
open Family8EndpointIdentityNoKTMiddleCallInputsV7
open Family8EndpointLongCoreIdentityIntervalCountsV3
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
open Family8FirstCrossingActiveIndexThirdBetaGammaRefoldV4
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8IdentityMassPopularContractedScaleBudgetV4
open Family8IdentityMassPopularNoKTConstantPowersV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8NoKTMiddleCallInputsV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFiberLowCFFreshCardEnvelopePowerV3
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Direct same-object LongCore data, conditional only on the displayed
scalar gates that are not fields of the existing endpoint witness. -/
theorem nonempty_longCoreThreeScaleDSOData_of_direct_noKT_middle_recomputedThird
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (targetEpsilon lossEta : Real)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    {etaSource frostmanEta epsilonThird etaThird : Real} {delta0 : NNReal}
    (hFsource : FrostmanHypotheses D etaSource)
    (hFmiddle : FrostmanAtParameters beta P.epsilon frostmanEta delta0)
    (hFthird : FrostmanAtParameters beta epsilonThird etaThird delta0)
    {lowerExp cardExp a cardAbsorbExp kappa globalEta : Real}
    (hcardExp : 0 <= cardExp) (hcountExp : 0 < 2 + kappa)
    (hcombined : 0 < lowerExp + cardExp)
    (ha : 0 < a) (hcardAbsorbExp : 0 < cardAbsorbExp)
    (hlowerPower :
      capturedTubeBoxLoss
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) <=
        (((contractedJohnProxyRadius
            ((endpointScaleSequence delta
              (hD.delta_le_half.trans (by norm_num))).tau W.m)
            (canonicalBufferedRadius W) / 8 : NNReal) : ENNReal) ^
          (-lowerExp)))
    {lossExp densityAbsorbExp baseAbsorbExp : Real}
    (hlossExp : 0 < lossExp)
    (hdensityAbsorbExp : 0 < densityAbsorbExp)
    (hbaseAbsorbExp : 0 < baseAbsorbExp)
    (hsmallLoss : delta <=
      activeFrozenComparableLossAbsorptionThreshold lossExp)
    (hsmallDensityConstant : delta <=
      identityMassPopularDensityPowerThreshold densityAbsorbExp)
    (hsmallBaseConstant : delta <=
      identityMassPopularBasePowerThreshold frostmanEta
        (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) a
        baseAbsorbExp)
    (hdensityGain : 0 <= frostmanEta -
      ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a))
    (hdensityExponentBudget :
      etaSource + lossExp + densityAbsorbExp <=
        P.epsilon ^ 2 *
          (frostmanEta -
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)))
    (hbaseGain : 0 <= frostmanEta -
      (2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a) - 2)
    (hbaseExponentBudget :
      etaSource + lossExp + baseAbsorbExp <=
        P.epsilon ^ 2 *
          (frostmanEta -
            (2 * (2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a) - 2))
    (hsmallFresh :
      contractedJohnProxyRadius
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) / 8 <=
        selectedParentLowCFFreshCardEnvelopePowerThreshold a cardAbsorbExp)
    (hproxyDelta0 :
      contractedJohnProxyRadius
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) / 8 <= delta0)
    (hsmallSource :
      contractedJohnProxyRadius
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) / 8 <=
        Family8StickyFiberContractedJohnSourcePowerEndpointV1.contractedJohnSourcePowerEndpointThreshold a)
    {middleAbsorbExp : Real}
    (hmiddleAbsorbExp : 0 < middleAbsorbExp)
    (hratioSmall :
      ((endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).tau W.m) /
          canonicalBufferedRadius W <=
        contractedJohnMiddleFourActualPowerThreshold
          1 P.epsilon beta gamma
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
            middleAbsorbExp)
    (hmiddleNet : 0 <=
      contractedJohnMiddleRatioGain
        P.epsilon beta gamma
          ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
          kappa - middleAbsorbExp)
    (hmiddleExponentBudget : 10 * globalEta <=
      P.epsilon ^ 2 *
        (contractedJohnMiddleRatioGain
          P.epsilon beta gamma
            ((2 * lowerExp + 2 * cardExp + a + cardAbsorbExp) + a)
            kappa - middleAbsorbExp))
    (hbetaTwo : beta <= 2) (hgammaTwo : gamma <= 2)
    (hbetaGamma : beta <= gamma)
    (hthirdDelta0 : canonicalBufferedRadius W / 8 <= delta0) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
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
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
      intro k _hk
      simpa only [Fintype.card_coe] using
        identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
          E hE S W P.epsilon_pos.le hepsilonHalf k
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
    let Pcoarse := boundedFiberCoarseTubePartition U
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
      hcoarse 1 hM
    let CKT := identitySourceFrostmanKatzTaoConstant D rho etaSource
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    (forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading ->
      (((rho / 8 : NNReal) : ENNReal) ^ etaThird *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2)))) ->
    (((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
        (delta : ENNReal) ^ (-etaSource) <=
      ((rho / 8 : NNReal) : ENNReal) ^ (-etaThird)) ->
    (((rho : ENNReal) ^ (4 : Nat)) *
        (activeCoarseCardScaleMass U : ENNReal) <= 1) ->
    (forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
      forall n : Nat,
        (4 * (A.loss : ENNReal)) *
            ((delta : ENNReal) ^ (10 * globalEta) *
              sectionEightScaleCountFrostmanFactor
                (S.tau W.m) rho n gamma) <=
          (delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (S.tau W.m) rho n gamma) ->
    (eighthSelectedThirdFactorLoss rho
        ((432 : ENNReal) *
          ((conflictThreshold + 1 : Nat) : ENNReal))
        epsilonThird beta <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage)) ->
    Nonempty (LongCoreThreeScaleDSOData D hD
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      P W targetEpsilon) := by
  dsimp only
  intro hdensityGate hbaseGate hcardScale hmiddleAbsorb hthirdPowerGate
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hrhoOne : rho <= 1 := by
    dsimp only [rho]
    exact canonicalBufferedRadius_le_one W hD.delta_pos
      P.epsilon_pos.le hepsilonHalf
  have hscale : S.tau W.m <= rho := by
    dsimp only [rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ :=
    hscale.trans (hbufferedSixteenth.trans (by
      change (1 : Real) / 16 <= (2 : Real)⁻¹
      norm_num))
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hFsource
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
    rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
      D hD P W hepsilonHalf]
    exact hmass
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  have hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le hepsilonHalf k
  have hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U hscale hcoarse 1 hM
  let CKT := identitySourceFrostmanKatzTaoConstant D rho etaSource
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  have hAssembly :=
    exists_endpointLongCore_canonicalBufferedTauActive_singletonExactOuterAssembly
      D hD P W hepsilonHalf hmass
  dsimp only at hAssembly
  obtain ⟨_hbranchLoss, _hbranch, A, hAloss, hfrozen,
      _k, _hk, _hpositive⟩ := hAssembly
  obtain ⟨_hq0, _hqTop, hqPower⟩ :=
    canonicalBufferedTauActive_ratio_power_inputs E hE C S P W
  have hratioDelta : (((S.tau W.m / rho : NNReal) : ENNReal)) <=
      (delta : ENNReal) ^ (P.epsilon ^ 2) := by
    simpa only [rho, ENNReal.coe_div hrho.ne'] using hqPower
  have hMiddle :=
    Family8NoKTMiddleCallInputsV2.CallInputs.exists_freshLongMiddle
      hFmiddle U Y 1 htau htauHalf hrho hrhoOne hscale hcoarse hM A
        (endpointLongCore_identity_noKT_callInputs
          D hD P W hepsilonHalf hFsource hcardExp hcountExp
            hlossExp hdensityAbsorbExp hbaseAbsorbExp hsmallLoss
            hsmallDensityConstant hsmallBaseConstant hdensityGain
            hdensityExponentBudget hbaseGain hbaseExponentBudget A hAloss)
        hcombined ha hcardAbsorbExp hsmallFresh hlowerPower hproxyDelta0
        hsmallSource (hglobalDeltaOne :=
          hD.delta_le_half.trans (by norm_num)) (hK0 := by norm_num)
        (hKTop := by norm_num) hmiddleAbsorbExp hratioSmall hratioDelta
        hmiddleNet hmiddleExponentBudget hbetaTwo hgammaTwo
          (sub_nonneg.mpr hbetaGamma)
  obtain ⟨q, selected, _hselected, hMiddleRaw⟩ := hMiddle
  have hXraw :=
    nonempty_endpointLongCore_identity_exactOuter_recomputedThird
      D hD P W hepsilonHalf hbufferedSixteenth hmass hFsource hFthird
        hbetaTwo hthirdDelta0
  dsimp only at hXraw
  have hX := hXraw A hfrozen (hdensityGate A hAloss hfrozen) hbaseGate
  obtain ⟨Xbeta⟩ := hX
  let Xgamma :=
    Family8FirstCrossingActiveIndexThirdBetaGammaRefoldV4.CoreNativeFrozenThirdBundle.toGammaOfActiveFineCardScale
      Dtau U0 Pcoarse Y A Xbeta hrho hbetaGamma hcardScale
  have hfine :
      Pcoarse.asConvexFactorization.index.fine = U.activeFine := by
    simpa only [Pcoarse] using
      boundedFiberCoarseTubePartition_asConvexFactorization_fine
        U hscale hcoarse 1 hM
  have hU : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  have hBounded :
      (IndexedShadingRefinement.restrictTo Y
        Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
          D.shading.averageMultiplicity := by
    calc
      (IndexedShadingRefinement.restrictTo Y
          Pcoarse.asConvexFactorization.index.fine).shading.averageMultiplicity =
          Y.averageMultiplicity := by
        rw [hfine, hU, restrictTo_univ_averageMultiplicity]
      _ = (activeFineShading U0 Dtau.shading).averageMultiplicity :=
        activeFineRestrictedShading_averageMultiplicity U0 Dtau.shading
      _ = Dtau.shading.averageMultiplicity :=
        canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
          E hE C S P W hepsilonHalf
      _ = D.shading.averageMultiplicity :=
        endpointLongCore_tauActive_averageMultiplicity_eq_source D hD P W
  have hcoarseCard :=
    endpointLongCore_activeFineRestricted_coarseCard_eq_indexCard
      D hD P W hepsilonHalf
  dsimp only at hcoarseCard
  let hindices := assembly_indices_subset_activeFine U Y 1 A
  have hThirdPower : Xgamma.thirdLoss <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
    simpa only [Xgamma, thirdLoss] using hthirdPowerGate
  exact nonempty_longCoreThreeScaleDSOData_of_selectedFine_middle_third
    D hD P W hdeltaBase U Y hscale hcoarse hM A rho hscale
      A.refinement.indices hindices q.1 selected hcoarseCard
      ((delta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) rho selected.card gamma)
      Xgamma (hTau := rfl) hBounded hMiddleRaw
      (hmiddleAbsorb A hAloss selected.card) hThirdPower

#print axioms
  nonempty_longCoreThreeScaleDSOData_of_direct_noKT_middle_recomputedThird

end
end Family8EndpointIdentityDirectNoKTMiddleRecomputedThirdDSOComposerV4

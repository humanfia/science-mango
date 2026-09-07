import Family8Grounding.Family8ActiveFrozenComparableLogLossAbsorptionV4
import Family8Grounding.Family8CanonicalEndpointBaseThresholdV1
import Family8Grounding.Family8EndpointIdentityDirectNoKTMiddleLossAutomaticV1
import Family8Grounding.Family8EndpointIdentityRecomputedThirdGammaAdapterV1
import Family8Grounding.Family8EndpointLongCoreIdentityIntervalCountsV3
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
import Family8Grounding.Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
import Family8Grounding.Family8EndpointSelectedFineSingletonDirectLongMiddleV2
import Family8Grounding.Family8FirstCrossingRecomputedThirdFullLossPowerV1
import Family8Grounding.Family8HighGammaParameterLadderV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveBasicTransportsV2
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Family8Grounding.Family8ParentwiseLongCoreCanonicalMassPopularCFConsumerConnectorV1
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Family8Grounding.Family8StickyBoundedFiberFactorizationRoundTripV2
import Family8Grounding.Family8StickySelectedFineAssemblyMassPopularV1
import Mathlib.Tactic

/-!
# Direct high-gamma LongCore DSO on the endpoint identity cover

The strict high-gamma reserve pays the complete singleton middle factor:
one quarter absorbs its literal coefficient four, while the remaining
quarters absorb the exact frozen-comparable assembly loss and its outer
coefficient.  The third factor is constructed natively at `gamma`, so this
route asks for no Frostman hypothesis at `beta` and performs no reverse
restriction or beta-to-gamma refold.

Only the two recomputed-third scalar gates and explicit small-scale/exponent
budgets remain assumptions.  In particular, no geometric conclusion is
passed as a callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8CanonicalEndpointBaseThresholdV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointIdentityDirectNoKTMiddleLossAutomaticV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityRecomputedThirdGammaAdapterV1
open Family8EndpointLongCoreIdentityIntervalCountsV3
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8EndpointLongCoreTauActiveSingletonExactOuterAssemblyV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8EndpointSelectedFineSameAssemblyDSOConnectorV3
open Family8EndpointSelectedFineSingletonDirectLongMiddleV2
open Family8FirstCrossingRecomputedThirdFullLossPowerV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8HighGammaParameterLadderV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentwiseLongCoreCanonicalMassPopularCFConsumerConnectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8SectionEightOutputEtaV1
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberFactorizationRoundTripV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyBoundedFiberPartitionFineIndexV3
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySelectedFineAssemblyFiberBridgeV1
open Family8StickySelectedFineAssemblyMassPopularV1
open Family8StickySelectedFineSubtypeScaleCoverV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The exponent reserve left after the stage power in the high-gamma
singleton middle estimate. -/
def longCoreHighGammaReserve
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : Real :=
  P.epsilon ^ 2 * (3 * gamma - 2) - 10 * P.eta stage

/-- One quarter of the reserve pays either a fixed coefficient or the
canonical logarithmic assembly loss. -/
def longCoreHighGammaQuarterReserve
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : Real :=
  longCoreHighGammaReserve P stage / 4

/-- An intermediate exponent whose excess over the stage exponent pays the
outer coefficient and the assembly loss. -/
def longCoreHighGammaMiddleEta
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : Real :=
  P.eta stage + longCoreHighGammaReserve P stage / 20

/-- One positive stage fraction is reserved for the fixed recomputed-third
loss. -/
def longCoreHighGammaThirdAbsorb
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : Real :=
  P.eta stage / 4

/-- The normalized endpoint view determined by one faithful parentwise core. -/
abbrev parentwiseEndpointNormalizedWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.epsilon_pos.le P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hFine :
      (fullRefinementDatum D).family.refinement.refined.Nonempty) :
    NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) :=
  Wparent.toNormalizedLongIntervalCoreWitness
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
    (identityRadiusCoherentCover (fullRefinementDatum D).family)
    (endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num)))
    P.epsilon_pos.le hFine

theorem dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (Wparent : ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.epsilon_pos.le P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hFine :
      (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (targetEpsilon lossEta sourceEta : Real) (delta0 : NNReal)
    (hTargetEpsilon : 0 < targetEpsilon)
    (hSourceEta : 0 < sourceEta)
    (hGammaOne : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius (parentwiseEndpointNormalizedWitness D hD P Wparent hFine) <= (1 / 16 : NNReal))
    (hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hFExact : FrostmanAtParameters
      gamma (targetEpsilon / 4) sourceEta delta0)
    (hhigh : 10 * P.eta (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage <
      P.epsilon ^ 2 * (3 * gamma - 2))
    (hsmallFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold
        (longCoreHighGammaQuarterReserve P (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage))
    (hsmallOuterFour : delta <=
      FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1.finiteConstantSmallDeltaThreshold
        (4 : ENNReal) (longCoreHighGammaQuarterReserve P (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage))
    (hsmallMiddleFour : delta <=
      FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1.finiteConstantSmallDeltaThreshold
        (4 : ENNReal) (longCoreHighGammaQuarterReserve P (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage))
    (hthirdDelta0 : canonicalBufferedRadius (parentwiseEndpointNormalizedWitness D hD P Wparent hFine) / 8 <= delta0)
    (hsmallThird : delta <=
      Family8FirstCrossingRecomputedThirdFixedLossPowerV3.recomputedThirdFixedLossPowerThreshold
        sourceEta (longCoreHighGammaThirdAbsorb P (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage)
          (targetEpsilon / 4) gamma)
    (hthirdBudget : sourceEta +
        longCoreHighGammaThirdAbsorb P (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage + targetEpsilon / 4 <=
      3 * P.eta (parentwiseEndpointNormalizedWitness D hD P Wparent hFine).stage) :
    let W := parentwiseEndpointNormalizedWitness D hD P Wparent hFine
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
      have hmass : D.shading.shadingMass ≠ 0 := by
        have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
          D hD hFOutput
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top).trans_le hfloor)
      have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
        rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
          D hD P W hepsilonHalf]
        exact hmass
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
    let CKT := identitySourceFrostmanKatzTaoConstant D rho
      (sectionEightOutputEta P sourceEta)
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    (forall A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        Pcoarse.asConvexFactorization Y 1,
      A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U.coarseCard) ->
      A.frozenCoarse =
          Pcoarse.asConvexFactorization.inducedShading
            A.refinement.shading ->
      (((rho / 8 : NNReal) : ENNReal) ^ sourceEta *
          (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2)))) ->
    (((conflictThreshold + 1 : Nat) : ENNReal) * 2097152 *
        (delta : ENNReal) ^
          (-(sectionEightOutputEta P sourceEta)) <=
      ((rho / 8 : NNReal) : ENNReal) ^ (-sourceEta)) ->
    DividingScaleOutput D P targetEpsilon := by
  dsimp only
  intro hdensityGate hbaseGate
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let W := parentwiseEndpointNormalizedWitness D hD P Wparent hFine
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hscale : S.tau W.m <= rho := by
    dsimp only [rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hdeltaRho : delta <= rho := (S.delta_le_tau W.m).trans hscale
  have hgammaTwo : gamma <= 2 := hGammaOne.trans (by norm_num)
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
      D hD hFOutput
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos)
      ENNReal.coe_ne_top).trans_le hfloor)
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
  let CKT := identitySourceFrostmanKatzTaoConstant D rho
    (sectionEightOutputEta P sourceEta)
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  let reserve := longCoreHighGammaReserve P W.stage
  let quarter := longCoreHighGammaQuarterReserve P W.stage
  let globalEta := longCoreHighGammaMiddleEta P W.stage
  let thirdAbsorb := longCoreHighGammaThirdAbsorb P W.stage
  have hreserve : 0 < reserve := by
    dsimp only [reserve, longCoreHighGammaReserve]
    linarith
  have hquarter : 0 < quarter := by
    dsimp only [quarter, longCoreHighGammaQuarterReserve]
    exact div_pos hreserve (by norm_num)
  have hthirdAbsorb : 0 < thirdAbsorb := by
    dsimp only [thirdAbsorb, longCoreHighGammaThirdAbsorb]
    exact div_pos (P.eta_pos W.stage) (by norm_num)
  have hglobalEta : 0 ≤ globalEta := by
    have hreserve' : 0 ≤ longCoreHighGammaReserve P W.stage := by
      simpa only [reserve] using hreserve.le
    dsimp only [globalEta, longCoreHighGammaMiddleEta]
    exact add_nonneg (P.eta_pos W.stage).le
      (div_nonneg hreserve' (by norm_num))
  have hAssembly :=
    exists_endpointLongCore_canonicalBufferedTauActive_singletonExactOuterAssembly
      D hD P W hepsilonHalf hmass
  dsimp only at hAssembly
  obtain ⟨_hbranchLoss, _hbranch, A, hAloss, hfrozen,
      _k, _hk, _hpositive⟩ := hAssembly
  let hindices := assembly_indices_subset_activeFine U Y 1 A
  let T := selectedFineScaleCover U A.refinement.indices hindices
  let Z := selectedFineShading U A.refinement.indices A.refinement.shading
  have hProductRaw :=
    exists_canonicalTauActiveRestricted_endpointConsumerTuple
      E hE C S P.epsilon_pos.le Wparent hFine hepsilonHalf
        Y 1 A hsource
  obtain ⟨q, _hOldActive, _hmassPopular, _hvolume, hproduct, _hcf⟩ :=
    hProductRaw
  let selected : Finset {i // i ∈ T.fiber q.1} := Finset.univ
  let oldParent : Fin U.coarseCard :=
    ((selectedFineParentValues U A.refinement.indices).equivFin.symm q.1).1
  have holdParent : oldParent ∈ U.activeCoarse := by
    dsimp only [oldParent]
    exact selectedFineScaleCover_parent_mem_activeCoarse
      U A.refinement.indices hindices q.1
  have hfiberCardLe : (T.fiber q.1).card <= 1 := by
    calc
      (T.fiber q.1).card <= (U.fiber oldParent).card := by
        simpa only [T, oldParent] using
          selectedFineScaleCover_fiber_card_le_parent_fiber
            U A.refinement.indices hindices q.1
      _ <= 1 := hM oldParent holdParent
  have hfiberNonempty : (T.fiber q.1).Nonempty := by
    obtain ⟨i, hi, hip⟩ := T.parent_surjective q.1 q.2
    exact ⟨i, (T.mem_fiber i q.1).2 ⟨hi, hip⟩⟩
  have hfiberCard : (T.fiber q.1).card = 1 := by
    have hpos : 0 < (T.fiber q.1).card := Finset.card_pos.mpr hfiberNonempty
    omega
  have hselectedCard : selected.card = 1 := by
    simpa only [selected, Finset.card_univ, Fintype.card_coe] using hfiberCard
  have havg : (stickyFiberSourceShading T Z q.1).averageMultiplicity <= 1 := by
    have havgRaw := averageMultiplicity_le_indexCard
      (stickyFiberSourceShading T Z q.1)
    simpa only [Fintype.card_coe, hfiberCard, Nat.cast_one] using havgRaw
  obtain ⟨_hq0, _hqTop, hqPower⟩ :=
    canonicalBufferedTauActive_ratio_power_inputs E hE C S P W
  have hratio : (S.tau W.m : ENNReal) / (rho : ENNReal) <=
      (delta : ENNReal) ^ (P.epsilon ^ 2) := by
    simpa only [rho, ENNReal.coe_div hrho.ne'] using hqPower
  have hratioExp : 0 < P.epsilon ^ 2 := sq_pos_of_pos P.epsilon_pos
  have hinnerBudget : 10 * globalEta + quarter <=
      (P.epsilon ^ 2) * (3 * gamma - 2) := by
    dsimp only [globalEta, quarter, longCoreHighGammaMiddleEta,
      longCoreHighGammaQuarterReserve, longCoreHighGammaReserve, reserve]
    linarith
  have hfour := four_le_globalPower_mul_sectionEight_singleton
    hD.delta_pos hdeltaOne htau hrho hgammaTwo
      hglobalEta hratioExp hratio
      hquarter hinnerBudget hsmallMiddleFour
  have havgMiddle : 4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity <=
      (delta : ENNReal) ^ (10 * globalEta) *
        sectionEightScaleCountFrostmanFactor
          (S.tau W.m) rho selected.card gamma := by
    calc
      4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity <= 4 := by
        simpa only [mul_one] using mul_le_mul' le_rfl havg
      _ <= (delta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor
            (S.tau W.m) rho 1 gamma := hfour
      _ = (delta : ENNReal) ^ (10 * globalEta) *
          sectionEightScaleCountFrostmanFactor
            (S.tau W.m) rho selected.card gamma := by rw [hselectedCard]
  have hMiddleRaw :
      (actualRefinementShading A).averageMultiplicity <=
        A.frozenCoarse.averageMultiplicity *
          (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
    calc
      (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
        exact hproduct
      _ = A.frozenCoarse.averageMultiplicity *
          (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity) := by
        ac_rfl
  have hLossRaw := canonicalBufferedTauActive_frozenLoss_le_power
    E hE C S P W hepsilonHalf hquarter hsmallFrozen
  have hLoss : (A.loss : ENNReal) <=
      (delta : ENNReal) ^ (-quarter) := by
    rw [hAloss]
    exact hLossRaw
  have houterBudget : 10 * P.eta W.stage + 2 * quarter <=
      10 * globalEta := by
    dsimp only [globalEta, quarter, longCoreHighGammaMiddleEta,
      longCoreHighGammaQuarterReserve, longCoreHighGammaReserve, reserve]
    linarith
  have hMiddleAbsorb :
      (4 * (A.loss : ENNReal)) *
          (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity) <=
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (S.tau W.m) rho selected.card gamma := by
    calc
      (4 * (A.loss : ENNReal)) *
          (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity) <=
        (4 * (A.loss : ENNReal)) *
          ((delta : ENNReal) ^ (10 * globalEta) *
            sectionEightScaleCountFrostmanFactor
              (S.tau W.m) rho selected.card gamma) :=
        mul_le_mul' le_rfl havgMiddle
      _ <= (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (S.tau W.m) rho selected.card gamma :=
        four_mul_loss_middleFactor_le_stageFactor
          hD.delta_pos hdeltaOne hquarter hsmallOuterFour hLoss houterBudget
  have hXraw :=
    nonempty_endpointLongCore_identity_exactOuter_recomputedThird_gamma
      D hD P W hepsilonHalf hbufferedSixteenth targetEpsilon sourceEta
        delta0 hFOutput hFExact hgammaTwo hthirdDelta0
  dsimp only at hXraw
  have hX := hXraw A hfrozen (hdensityGate A hAloss hfrozen) hbaseGate
  obtain ⟨X⟩ := hX
  have hThirdPowerRaw :=
    recomputedThird_fullLoss_le_delta_negativePower
      hD.delta_pos hdeltaOne hrho hdeltaRho
      (sectionEightOutputEta_pos P hSourceEta).le hSourceEta.le
      hthirdAbsorb (div_nonneg hTargetEpsilon.le (by norm_num))
      hbaseGate hsmallThird hthirdBudget
  have hThirdPower : X.thirdLoss <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
    simpa only [thirdLoss, thirdAbsorb, rho, neg_mul] using hThirdPowerRaw
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
  have hData := nonempty_longCoreThreeScaleDSOData_of_selectedFine_middle_third
    D hD P W hdeltaBase U Y hscale hcoarse hM A rho hscale
      A.refinement.indices hindices q.1 selected hcoarseCard
      (4 * (stickyFiberSourceShading T Z q.1).averageMultiplicity)
      X (hTau := rfl) hBounded hMiddleRaw hMiddleAbsorb hThirdPower
  obtain ⟨data⟩ := hData
  exact data.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore

end
end Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1

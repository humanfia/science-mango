import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1
import Family8Grounding.Family8EndpointIdentityParentwiseFirstCrossingImpossibleV1
import Mathlib.Tactic

/-!
# Automatic endpoint parentwise LongCore to high-gamma DSO

The endpoint parentwise selector now has no residual stopping branch below its
explicit threshold.  This module chooses that produced witness, derives the
full-refinement nonemptiness needed by the compatibility projection from the
already assumed Frostman output hypothesis, and invokes the parentwise
high-gamma DSO on those literal objects.

The legacy normalized witness is definitionally the projection of the chosen
parentwise witness.  The optimized product API uses that same definitional
view directly, with no equality transport.  All of its analytic and scalar
hypotheses remain explicit.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalEndpointBaseThresholdV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1
open Family8EndpointIdentityParentwiseFirstCrossingImpossibleV1
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FullRefinementActualDatumV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1.ParentwiseNormalizedLongIntervalCoreWitness
open Family8SectionEightOutputEtaV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyParentPopularCanonicalUnionV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- A Frostman output hypothesis forces positive source shading mass, hence the
literal full refinement (whose refined set is `univ`) is nonempty. -/
theorem fullRefinement_refined_nonempty_of_frostmanHypotheses
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {outputEta : Real} (hF : FrostmanHypotheses D outputEta) :
    (fullRefinementDatum D).family.refinement.refined.Nonempty := by
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top).trans_le hfloor)
  let hindex : Nonempty index :=
    nonempty_of_shadingMass_pos D.shading (bot_lt_iff_ne_bot.mpr hmass)
  rw [fullRefinementDatum_refined]
  let i : index := Classical.choice hindex
  exact ⟨i, Finset.mem_univ i⟩

/-- The concrete parentwise LongCore selected by the fully internal endpoint
trichotomy and its literal-parent crossing elimination. -/
noncomputable def automaticParentwiseLongCoreWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P) :
    ParentwiseNormalizedLongIntervalCoreWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.epsilon_pos.le P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) :=
  Classical.choice
    (endpointIdentity_fullRefinement_parentwiseLongCore_of_small
      D hD P hbeta hGammaOne hselectorSmall)

/-- The established normalized witness used by analytic endpoint consumers,
defined to be the compatibility projection of the chosen parentwise witness. -/
noncomputable def automaticNormalizedLongCoreWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hF : FrostmanHypotheses D outputEta) :
    NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) :=
  parentwiseEndpointNormalizedWitness D hD P
    (automaticParentwiseLongCoreWitness
      D hD P hbeta hGammaOne hselectorSmall)
    (fullRefinement_refined_nonempty_of_frostmanHypotheses D hD hF)

/-- Below the explicit parentwise stopping threshold, the endpoint selector and
literal-parent crossing contradiction are automatic.  The remaining inputs
are exactly the analytic and scalar hypotheses of the parentwise high-gamma
LongCore product theorem. -/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore_automatic
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon lossEta sourceEta : Real) (delta0 : NNReal)
    (hbeta : 0 < beta)
    (hTargetEpsilon : 0 < targetEpsilon)
    (hSourceEta : 0 < sourceEta)
    (hGammaOne : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    (hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P targetEpsilon lossEta)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hFExact : FrostmanAtParameters
      gamma (targetEpsilon / 4) sourceEta delta0)
    (hbufferedSixteenth : canonicalBufferedRadius
        (automaticNormalizedLongCoreWitness
          D hD P hbeta hGammaOne hselectorSmall hFOutput) <=
      (1 / 16 : NNReal))
    (hhigh : 10 * P.eta
        (automaticNormalizedLongCoreWitness
          D hD P hbeta hGammaOne hselectorSmall hFOutput).stage <
      P.epsilon ^ 2 * (3 * gamma - 2))
    (hsmallFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold
        (longCoreHighGammaQuarterReserve P
          (automaticNormalizedLongCoreWitness
            D hD P hbeta hGammaOne hselectorSmall hFOutput).stage))
    (hsmallOuterFour : delta <=
      FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1.finiteConstantSmallDeltaThreshold
        (4 : ENNReal) (longCoreHighGammaQuarterReserve P
          (automaticNormalizedLongCoreWitness
            D hD P hbeta hGammaOne hselectorSmall hFOutput).stage))
    (hsmallMiddleFour : delta <=
      FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1.finiteConstantSmallDeltaThreshold
        (4 : ENNReal) (longCoreHighGammaQuarterReserve P
          (automaticNormalizedLongCoreWitness
            D hD P hbeta hGammaOne hselectorSmall hFOutput).stage))
    (hthirdDelta0 : canonicalBufferedRadius
        (automaticNormalizedLongCoreWitness
          D hD P hbeta hGammaOne hselectorSmall hFOutput) / 8 <= delta0)
    (hsmallThird : delta <=
      Family8FirstCrossingRecomputedThirdFixedLossPowerV3.recomputedThirdFixedLossPowerThreshold
        sourceEta (longCoreHighGammaThirdAbsorb P
          (automaticNormalizedLongCoreWitness
            D hD P hbeta hGammaOne hselectorSmall hFOutput).stage)
          (targetEpsilon / 4) gamma)
    (hthirdBudget : sourceEta +
        longCoreHighGammaThirdAbsorb P
          (automaticNormalizedLongCoreWitness
            D hD P hbeta hGammaOne hselectorSmall hFOutput).stage +
          targetEpsilon / 4 <=
      3 * P.eta
        (automaticNormalizedLongCoreWitness
          D hD P hbeta hGammaOne hselectorSmall hFOutput).stage) :
    let W := automaticNormalizedLongCoreWitness
      D hD P hbeta hGammaOne hselectorSmall hFOutput
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
        Family8IdentityCoreTauActiveSingletonFiberV4.identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
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
  exact dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore
    D hD P
      (automaticParentwiseLongCoreWitness
        D hD P hbeta hGammaOne hselectorSmall)
      (fullRefinement_refined_nonempty_of_frostmanHypotheses D hD hFOutput)
      targetEpsilon lossEta sourceEta delta0
      hTargetEpsilon hSourceEta hGammaOne hepsilonHalf
      hbufferedSixteenth hdeltaBase hFOutput hFExact hhigh
      hsmallFrozen hsmallOuterFour hsmallMiddleFour hthirdDelta0
      hsmallThird hthirdBudget

#print axioms fullRefinement_refined_nonempty_of_frostmanHypotheses
#print axioms automaticParentwiseLongCoreWitness
#print axioms automaticNormalizedLongCoreWitness
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore_automatic

end
end Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1

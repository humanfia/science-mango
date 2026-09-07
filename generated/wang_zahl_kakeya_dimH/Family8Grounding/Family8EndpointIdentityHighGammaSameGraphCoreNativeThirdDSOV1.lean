import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8EndpointLongCoreIdentityIntervalCountsV3
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Family8Grounding.Family8ThreeScaleActualFrostmanFactorAbsorptionV2
import Mathlib.Tactic

/-!
# Endpoint same-graph singleton middle with a Core-native third factor

At the endpoint identity cover every canonical buffered fibre is a singleton.
Once source retention and the graph certificate's `same_product` estimate have
been combined, the honest middle factor is therefore just `A.loss * 4`.
This file connects that loss-free triple to the literal long-core three-scale
consumer.  The graph loss and `collapsedPrefix` are not used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreIdentityIntervalCountsV3
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Consume the graph-loss-free singleton triple on one literal endpoint
graph and one literal Core-native third bundle.

The three counts are definitionally `1`, `1`, and the canonical coarse-card;
the latter is the original source-card at the endpoint.  Consequently the
count loss is one, and the aggregate field is exactly the supplied third-loss
power. -/
theorem dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_coreNativeThird
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {fibreCF thirdLoss : ENNReal}
    (Q :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let F := activeFineRestrictedFamily U0
      let U := activeFineRestrictedScaleCover U0
      ConvexFactorization F.bodyFamily U.coarse.bodyFamily)
    (Y :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let F := activeFineRestrictedFamily U0
      Shading F.bodyFamily)
    (R :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let F := activeFineRestrictedFamily U0
      let U := activeFineRestrictedScaleCover U0
      SameAssemblyFullCoefficientGraphIdentity F U Q Y fibreCF)
    (X : CoreNativeFrozenThirdBundle Q Y R.A
      (canonicalBufferedRadius W) thirdLoss gamma)
    (hTriple : D.shading.averageMultiplicity <=
      1 * (((R.A.loss : ENNReal) * 4) *
        R.A.frozenCoarse.averageMultiplicity))
    (hMiddle : (R.A.loss : ENNReal) * 4 <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) 1 gamma)
    (hThirdPower : X.thirdLoss <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput D P targetEpsilon := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  have hcoarseCard : U.coarseCard = Fintype.card index := by
    simpa only [U, U0, C, S, E, hE] using
      endpointLongCore_activeFineRestricted_coarseCard_eq_indexCard
        D hD P W hepsilonHalf
  have hThirdCount : X.thirdCount = Fintype.card index := by
    change Fintype.card (Fin U.coarseCard) = Fintype.card index
    simpa only [Fintype.card_fin] using hcoarseCard
  have hCount :
      (((1 * (1 * X.thirdCount) : Nat) : ENNReal) <=
        (1 : ENNReal) * (Fintype.card index : ENNReal)) := by
    rw [hThirdCount]
    simp
  have hAggregate :
      (((1 : ENNReal) * X.thirdLoss) *
          (1 : ENNReal) ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage)) := by
    simpa using hThirdPower
  have hFirstFactor :
      sectionEightScaleCountFrostmanFactor delta (S.tau W.m) 1 gamma = 1 := by
    have hTau : S.tau W.m = delta := by rfl
    rw [hTau]
    exact sectionEightScaleCountFrostmanFactor_self_one hD.delta_pos gamma
  let data : LongCoreThreeScaleDSOData
      D hD C S P W targetEpsilon :=
    { middleScale := canonicalBufferedRadius W
      hTauMiddle :=
        tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
      firstCount := 1
      middleCount := 1
      thirdCount := X.thirdCount
      countLoss := 1
      hCount := hCount
      hSmall := hSmall
      firstAverage := 1
      middleAverage := (R.A.loss : ENNReal) * 4
      thirdAverage := R.A.frozenCoarse.averageMultiplicity
      firstLoss := 1
      thirdLoss := X.thirdLoss
      hTriple := hTriple
      hFirst := by rw [one_mul, hFirstFactor]
      hMiddle := by simpa only [S] using hMiddle
      hThird := by
        simpa only [CoreNativeFrozenThirdBundle.thirdAverage] using X.hThird
      hAggregateLoss := hAggregate }
  exact data.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms
  dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_coreNativeThird

end
end Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1

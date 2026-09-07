import Family8Grounding.Family8CanonicalGraphFrozenEndpointLossFreeSameRRawEq66V1
import Family8Grounding.Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Mathlib.Tactic

/-!
# Bounded-factorization endpoint same-graph DSO connector

This is the direct composition of the endpoint loss-free raw product with the
literal three-scale DSO consumer.  It is conditional only on the scalar middle
and third-loss power fields and the final Section-8 scale threshold.  In
particular it does not invoke a canonical-constant producer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdBoundedDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenEndpointLossFreeSameRRawEq66V1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdDSOV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
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

/-- Close the endpoint DSO on the exact bounded factorization and the exact
`R.A` used by a supplied Core-native third bundle.  Source retention and the
singleton-fibre product are proved internally; no raw `collapsedPrefix`
inequality is consumed. -/
theorem dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_bounded_coreNativeThird
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
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
          Pcoarse.asConvexFactorization Y fibreCF)
        (X : CoreNativeFrozenThirdBundle Pcoarse.asConvexFactorization Y R.A
          (canonicalBufferedRadius W) thirdLoss gamma),
        ((R.A.loss : ENNReal) * 4 <=
          (delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              (S.tau W.m) (canonicalBufferedRadius W) 1 gamma) ->
        X.thirdLoss <= (delta : ENNReal) ^ (-3 * P.eta W.stage) ->
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
  intro fibreCF thirdLoss R X hMiddle hThirdPower
  have hTripleRaw := endpointLongCore_identity_sameGraph_lossFour_rawEq66
    D hD P W hepsilonHalf
  dsimp only at hTripleRaw
  have hTriple := hTripleRaw M hM hcoarse fibreCF R
  exact
    dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_coreNativeThird
      D hD P W hepsilonHalf Pcoarse.asConvexFactorization Y R X hTriple
        hMiddle hThirdPower hSmall hTargetEpsilon hGammaOne

#print axioms
  dividingScaleOutput_of_endpointIdentity_sameGraph_lossFree_bounded_coreNativeThird

end
end Family8EndpointIdentityHighGammaSameGraphCoreNativeThirdBoundedDSOV1

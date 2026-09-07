import Family8Grounding.Family8CanonicalGraphFrozenCoreNativeThirdDSOV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstAggregatePowerV1
import Mathlib.Tactic

/-!
# Run-free Core-native third terminal with explicit power bookkeeping

This is the shortest scalar wrapper around the correctly factored canonical
graph terminal.  The middle estimate controls the literal collapsed prefix,
the third estimate comes from the same assembly's `CoreNativeFrozenThirdBundle`,
and a power bound for that bundle loss plus a power bound for the normalized
count loss automatically discharge the aggregate ledger.

There is no paper-factor run or final-state object in this interface.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenCoreNativeThirdExplicitPowerDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenCoreNativeThirdDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstAggregatePowerV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- The direct-middle/Core-native-third DSO terminal with the aggregate loss
derived from explicit third/count powers. -/
theorem dividingScaleOutput_of_sameGraph_gainedMiddle_coreNativeThird_explicitPowers
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    {fineIndex : Type} [Fintype fineIndex] [DecidableEq fineIndex]
    (fine : UniformTubeFamily (Sseq.tau W.m) fineIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real)
    (middleCount : Nat) {thirdLoss countLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y R.A
      (canonicalBufferedRadius W) thirdLoss gamma)
    (hTauEq : Sseq.tau W.m = delta)
    (hTauMiddle : Sseq.tau W.m <= canonicalBufferedRadius W)
    (hGainedMiddle :
      R.collapsedPrefix (delta := delta) firstCap lossEta <=
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            (Sseq.tau W.m) (canonicalBufferedRadius W) middleCount gamma)
    (hCount :
      ((1 * (middleCount * X.thirdCount) : Nat) : ENNReal) <=
        countLoss * (Fintype.card sourceIndex : ENNReal))
    {thirdExponent countExponent : Real}
    (hThirdPower : X.thirdLoss <=
      (delta : ENNReal) ^ (-thirdExponent))
    (hCountPower : countLoss <=
      (delta : ENNReal) ^ (-countExponent))
    (hExponentBudget : thirdExponent +
      countExponent * (1 - gamma / 2) <= 3 * P.eta W.stage)
    (hRawEq66 : Dsource.shading.averageMultiplicity <=
      R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hAggregate :
      ((1 : ENNReal) * X.thirdLoss) *
          countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage) :=
    identityFirst_thirdCountAggregateLoss_le_threeEta
      hDsource.delta_pos (hDsource.delta_le_half.trans (by norm_num))
      (hGammaOne.trans (by norm_num)) hThirdPower hCountPower
      hExponentBudget
  exact dividingScaleOutput_of_sameGraph_gainedMiddle_coreNativeThird_rawEq66
    (targetEpsilon := targetEpsilon)
    Dsource hDsource Cmulti Sseq P W fine U Q Y fibreCF R firstCap lossEta
      middleCount X hTauEq hTauMiddle hGainedMiddle hCount hRawEq66
      hAggregate hSmall hTargetEpsilon hGammaOne

#print axioms
  dividingScaleOutput_of_sameGraph_gainedMiddle_coreNativeThird_explicitPowers

end
end Family8CanonicalGraphFrozenCoreNativeThirdExplicitPowerDSOV1

import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Mathlib.Tactic

/-!
# Canonical graph middle gain with a Core-native third factor

The raw canonical-graph Equation (66) has the literal form

`sourceAverage <= collapsedPrefix * frozenCoarse.averageMultiplicity`.

The graph prefix is the middle average.  Its genuine analytic obligation is
therefore the gained middle estimate, while the frozen-coarse average belongs
to the third scale and is paid by `CoreNativeFrozenThirdBundle.bound`.  This
connector records that factor assignment directly.  In particular, the
frozen average is not treated as a ledger loss and no H-row automatic factor
is inserted into the prefix.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenCoreNativeThirdDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
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

/-- Close the long-core DSO from the honest three-factor assignment on one
literal canonical graph:

* the unit endpoint factor is the first average;
* the actual collapsed graph prefix is the middle average and carries the
  `delta^(10 eta)` gain;
* the same assembly's frozen-coarse average is the third average, bounded by
  the supplied Core-native third bundle.

`hTauEq` is the endpoint identity supplied by the endpoint long-core witness.
No frozen-average-to-row-factor comparison or payment of the frozen average
by the loss ledger occurs in this theorem. -/
theorem dividingScaleOutput_of_sameGraph_gainedMiddle_coreNativeThird_rawEq66
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
    (hRawEq66 : Dsource.shading.averageMultiplicity <=
      R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity)
    (hAggregateLoss :
      ((1 : ENNReal) * X.thirdLoss) * countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage))
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon)
    (hGammaOne : gamma <= 1) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hFirstFactor :
      sectionEightScaleCountFrostmanFactor
        delta (Sseq.tau W.m) 1 gamma = 1 := by
    rw [hTauEq]
    exact sectionEightScaleCountFrostmanFactor_self_one
      hDsource.delta_pos gamma
  let T : LongCoreThreeScaleDSOData
      Dsource hDsource Cmulti Sseq P W targetEpsilon :=
    { middleScale := canonicalBufferedRadius W
      hTauMiddle := hTauMiddle
      firstCount := 1
      middleCount := middleCount
      thirdCount := X.thirdCount
      countLoss := countLoss
      hCount := hCount
      hSmall := hSmall
      firstAverage := 1
      middleAverage :=
        R.collapsedPrefix (delta := delta) firstCap lossEta
      thirdAverage := R.A.frozenCoarse.averageMultiplicity
      firstLoss := 1
      thirdLoss := X.thirdLoss
      hTriple := by simpa only [one_mul] using hRawEq66
      hFirst := by rw [one_mul, hFirstFactor]
      hMiddle := hGainedMiddle
      hThird := by
        simpa only [CoreNativeFrozenThirdBundle.thirdAverage] using X.hThird
      hAggregateLoss := hAggregateLoss }
  exact T.toDividingScaleOutput hTargetEpsilon hGammaOne

#print axioms
  dividingScaleOutput_of_sameGraph_gainedMiddle_coreNativeThird_rawEq66

end
end Family8CanonicalGraphFrozenCoreNativeThirdDSOV1

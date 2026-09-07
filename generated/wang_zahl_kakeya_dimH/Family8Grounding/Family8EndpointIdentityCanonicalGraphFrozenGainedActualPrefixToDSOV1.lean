import Family8Grounding.Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3

/-!
# Endpoint specialization of the gained actual-prefix terminal

The generic gained-prefix terminal is formulated for an arbitrary coherent
multiscale cover and finite scale sequence.  The correlated Family-8 top
callback, however, uses the literal identity cover and the one-step endpoint
sequence.  This file specializes the terminal to exactly those objects.

In particular, the source-to-middle scale premise is discharged internally:
on the endpoint sequence the lower scale is `delta`, and the canonical
buffered radius is already known to contain that scale.  The remaining
arguments are therefore genuine same-assembly/run-ledger data, not a hidden
choice of a different long core.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCanonicalGraphFrozenGainedActualPrefixToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- The gained actual-prefix terminal on the literal endpoint identity core.

Compared with the generic terminal, this interface has no free coherent
cover, scale sequence, depth, or `hTauMiddle` premise.  Every other premise
is passed unchanged, so this theorem also serves as an exact audit of what
still has to be produced before the endpoint high branch is closed. -/
theorem dividingScaleOutput_of_endpointIdentity_sameAssembly_coreNativeThird_gainedActualPrefix
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family
      (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hDsource.delta_le_half.trans (by norm_num))))
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      (identityRadiusCoherentCover
        (fullRefinementDatum Dsource).family).base
      sourceDef212Constant)
    {fineIndex : Type} [Fintype fineIndex] [DecidableEq fineIndex]
    (fine : UniformTubeFamily
      ((endpointScaleSequence delta
        (hDsource.delta_le_half.trans (by norm_num))).tau W.m) fineIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    {bundleLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y R.A
      (canonicalBufferedRadius W) bundleLoss gamma)
    {runN sourceStage finalStage : Nat} {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource
        (identityRadiusCoherentCover (fullRefinementDatum Dsource).family)
        sourceDef212Constant sourceExact) finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 <= uniformityExp)
    (hFreshExp : 0 <= freshExp)
    (hUniformity : forall step, step ∈ run.productLedger.steps ->
      step.uniformityLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : forall step, step ∈ run.productLedger.steps ->
      step.freshRetentionLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp))
    (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * U.coarseCard : Nat) : ENNReal))
    (firstCap : ENNReal) (lossEta : Real)
    (hGainedPrefix :
      R.collapsedPrefix (delta := delta) firstCap lossEta <=
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          (coreNativeResidualFirstLoss run.productLedger X.thirdLoss *
            sectionEightScaleCountFrostmanFactor
              delta (canonicalBufferedRadius W) middleCount gamma))
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) <=
        3 * P.eta W.stage)
    (hRawEq66 : Dsource.shading.averageMultiplicity <=
      R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity)
    (hGammaOne : gamma <= 1)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  let C := identityRadiusCoherentCover
    (fullRefinementDatum Dsource).family
  let S := endpointScaleSequence delta
    (hDsource.delta_le_half.trans (by norm_num))
  have hTauMiddle : S.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hDsource.delta_pos P.epsilon_pos.le
  exact
    dividingScaleOutput_of_sameAssembly_coreNativeThird_gainedActualPrefix
      (targetEpsilon := targetEpsilon)
      Dsource hDsource C sourceDef212Constant sourceExact S P W
        fine U Q Y fibreCF R X run hUniformityExp hFreshExp
        hUniformity hFresh middleCount final_cardProduct_eq firstCap lossEta
        hGainedPrefix hExponentBudget hRawEq66 hTauMiddle hGammaOne
        hSmall hTargetEpsilon

#print axioms
  dividingScaleOutput_of_endpointIdentity_sameAssembly_coreNativeThird_gainedActualPrefix

end
end Family8EndpointIdentityCanonicalGraphFrozenGainedActualPrefixToDSOV1

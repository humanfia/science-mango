import Family8Grounding.Family8CanonicalGraphFrozenActiveParentRecoveryV1
import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
import Family8Grounding.Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
import Family8Grounding.Family8PaperFactorFiniteRunPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Canonical graph with a gained actual prefix and Core-native third bundle

The raw Equation-(66) prefix is multiplied by `delta^(-10 eta)`.  This moves
the middle gain into the actual-prefix field while leaving the Core-native
third loss unchanged.  The first ledger loss is then the reverse ledger
divided by that literal third loss, so its product payment is automatic.

Consequently the only analytic prefix premise is

`rawPrefix <= delta^(10 eta) * (firstLoss * middleSectionEightFactor)`.

The raw Equation-(66) estimate and the third bundle share the exact frozen
assembly `R.A`.  No displayed coefficient or H-row factor occurs here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenActiveParentRecoveryV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CoreNativeFrozenThirdBundleV1
open Family8CoreNativeFrozenThirdBundleV1.CoreNativeFrozenThirdBundle
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1.NormalizedLongCoreActualPrefixEq66Inputs
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-! ## Exact scalar allocation -/

/-- The actual prefix after moving the inverse middle gain into it. -/
def gainedActualPrefix
    (delta : NNReal) (eta : Real) (rawPrefix : ENNReal) : ENNReal :=
  (delta : ENNReal) ^ (-10 * eta) * rawPrefix

/-- The reverse-ledger residual after assigning one literal Core-native
third loss. -/
def coreNativeResidualFirstLoss
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (thirdLoss : ENNReal) : ENNReal :=
  cumulativeReverseLoss ledger / thirdLoss

/-- The quotient residual and the literal third loss are always paid by the
reverse ledger, without positivity or finiteness side assumptions. -/
theorem coreNativeResidualFirst_mul_third_le_reverse
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (thirdLoss : ENNReal) :
    coreNativeResidualFirstLoss ledger thirdLoss * thirdLoss ≤
      cumulativeReverseLoss ledger := by
  rw [coreNativeResidualFirstLoss, mul_comm]
  exact ENNReal.mul_div_le

/-- Convert the gained raw-prefix inequality into the exact actual-prefix
budget stored by the terminal record. -/
theorem gainedActualPrefix_le_of_raw_le_gain_mul
    (hdelta : 0 < delta) (eta : Real) {rawPrefix target : ENNReal}
    (hRaw : rawPrefix ≤ (delta : ENNReal) ^ (10 * eta) * target) :
    gainedActualPrefix delta eta rawPrefix ≤ target := by
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hcancel :
      (delta : ENNReal) ^ (-10 * eta) *
          (delta : ENNReal) ^ (10 * eta) = 1 := by
    rw [← ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
    have hExp : -10 * eta + 10 * eta = 0 := by ring
    rw [hExp, ENNReal.rpow_zero]
  calc
    gainedActualPrefix delta eta rawPrefix =
        (delta : ENNReal) ^ (-10 * eta) * rawPrefix := rfl
    _ ≤ (delta : ENNReal) ^ (-10 * eta) *
        ((delta : ENNReal) ^ (10 * eta) * target) :=
      mul_le_mul' le_rfl hRaw
    _ = ((delta : ENNReal) ^ (-10 * eta) *
          (delta : ENNReal) ^ (10 * eta)) * target := by ac_rfl
    _ = target := by rw [hcancel, one_mul]

/-! ## Grounded ledger to the minimal actual-prefix record -/

/-- Assemble the minimal terminal record.  The reverse-ledger product
payment is discharged by the quotient allocation above; only the gained
prefix inequality remains as an analytic input. -/
def groundedRun_normalizedActualPrefixEq66InputsOfCoreNativeGainedPrefix
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs Cmulti.base sourceDef212Constant)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {fineBody : ConvexFamily fineIndex} {coarseBody : ConvexFamily coarseIndex}
    {Q : ConvexFactorization fineBody coarseBody}
    {Y : Shading fineBody}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    {middleScale : NNReal} {bundleLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y A middleScale bundleLoss gamma)
    {runN sourceStage finalStage : Nat} {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 ≤ uniformityExp)
    (hFreshExp : 0 ≤ freshExp)
    (hUniformity : ∀ step, step ∈ run.productLedger.steps →
      step.uniformityLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : ∀ step, step ∈ run.productLedger.steps →
      step.freshRetentionLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp))
    (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * X.thirdCount : Nat) : ENNReal))
    (rawPrefix : ENNReal)
    (hGainedPrefix : rawPrefix ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        (coreNativeResidualFirstLoss run.productLedger X.thirdLoss *
          sectionEightScaleCountFrostmanFactor
            delta middleScale middleCount gamma))
    (hGammaTwo : gamma ≤ 2)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage) :
    NormalizedLongCoreActualPrefixEq66Inputs
      Dsource hDsource Cmulti Sseq P W := by
  let firstLedgerLoss :=
    coreNativeResidualFirstLoss run.productLedger X.thirdLoss
  let thirdLedgerLoss := X.thirdLoss
  let countLedgerLoss := cumulativeForwardLoss run.productLedger
  let ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount X.thirdCount
        firstLedgerLoss thirdLedgerLoss countLedgerLoss :=
    groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
      Dsource hDsource Cmulti sourceDef212Constant sourceExact run
        middleCount X.thirdCount firstLedgerLoss thirdLedgerLoss
          final_cardProduct_eq (by
            simpa only [firstLedgerLoss, thirdLedgerLoss] using
              coreNativeResidualFirst_mul_third_le_reverse
                run.productLedger X.thirdLoss)
  have hPowers :=
    power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
      run hUniformityExp hFreshExp hUniformity hFresh
  have hCountAggregate :=
    count_and_aggregate_fields_of_repeatedBadParentLedger
      Dsource hDsource Cmulti Sseq P W run.productLedger middleCount
        X.thirdCount firstLedgerLoss thirdLedgerLoss countLedgerLoss
          ledgerId hGammaTwo hPowers.1 hPowers.2 hExponentBudget
  exact
    { middleScale := middleScale
      middleCount := middleCount
      thirdCount := X.thirdCount
      collapsedPrefix := gainedActualPrefix
        delta (P.eta W.stage) rawPrefix
      firstLoss := firstLedgerLoss
      thirdLoss := thirdLedgerLoss
      countLoss := countLedgerLoss
      actualPrefixBudget := by
        simpa only [firstLedgerLoss] using
          gainedActualPrefix_le_of_raw_le_gain_mul
            hDsource.delta_pos (P.eta W.stage) hGainedPrefix
      hCount := hCountAggregate.1
      hAggregateLoss := hCountAggregate.2 }

/-! ## Same-assembly raw triple -/

/-- The raw graph product and `X.bound` become the terminal triple after the
gain in the actual prefix cancels the displayed positive gain exactly. -/
theorem hTriple_of_rawEq66_coreNativeThird_gainedActualPrefix
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {fineBody : ConvexFamily fineIndex} {coarseBody : ConvexFamily coarseIndex}
    {Q : ConvexFactorization fineBody coarseBody}
    {Y : Shading fineBody}
    {A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1}
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (Z : NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W)
    {middleScale : NNReal} {bundleLoss rawPrefix : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y A middleScale bundleLoss gamma)
    (hMiddleScale : Z.middleScale = middleScale)
    (hThirdCount : Z.thirdCount = X.thirdCount)
    (hThirdLoss : Z.thirdLoss = X.thirdLoss)
    (hCollapsed : Z.collapsedPrefix =
      gainedActualPrefix delta (P.eta W.stage) rawPrefix)
    (hRawEq66 : D.shading.averageMultiplicity ≤
      rawPrefix * A.frozenCoarse.averageMultiplicity) :
    D.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hcancel :
      (delta : ENNReal) ^ (-10 * P.eta W.stage) *
          (delta : ENNReal) ^ (10 * P.eta W.stage) = 1 := by
    rw [← ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
    have hExp :
        -10 * P.eta W.stage + 10 * P.eta W.stage = 0 := by ring
    rw [hExp, ENNReal.rpow_zero]
  calc
    D.shading.averageMultiplicity ≤
        rawPrefix * A.frozenCoarse.averageMultiplicity := hRawEq66
    _ ≤ rawPrefix *
        (X.thirdLoss * sectionEightScaleCountFrostmanFactor
          middleScale 1 X.thirdCount gamma) :=
      mul_le_mul' le_rfl X.hThird
    _ = Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
      rw [hMiddleScale, hThirdCount, hThirdLoss, hCollapsed,
        gainedActualPrefix]
      calc
        rawPrefix *
            (X.thirdLoss * sectionEightScaleCountFrostmanFactor
              middleScale 1 X.thirdCount gamma) =
            ((delta : ENNReal) ^ (-10 * P.eta W.stage) *
                (delta : ENNReal) ^ (10 * P.eta W.stage)) *
              (rawPrefix *
                (X.thirdLoss * sectionEightScaleCountFrostmanFactor
                  middleScale 1 X.thirdCount gamma)) := by
          rw [hcancel, one_mul]
        _ = ((delta : ENNReal) ^ (-10 * P.eta W.stage) * rawPrefix) *
            (((delta : ENNReal) ^ (10 * P.eta W.stage) *
                sectionEightScaleCountFrostmanFactor
                  middleScale 1 X.thirdCount gamma) * X.thirdLoss) := by
          ac_rfl

/-! ## Canonical exact same-assembly E2E -/

/-- Close the long-core DSO with one Core-native bundle on exactly `R.A`.
Besides the run/cardinality provenance and its power envelopes, the sole
analytic prefix premise is `hGainedPrefix`. -/
theorem dividingScaleOutput_of_sameAssembly_coreNativeThird_gainedActualPrefix
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs Cmulti.base sourceDef212Constant)
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
    {bundleLoss : ENNReal}
    (X : CoreNativeFrozenThirdBundle Q Y R.A
      (canonicalBufferedRadius W) bundleLoss gamma)
    {runN sourceStage finalStage : Nat} {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 ≤ uniformityExp)
    (hFreshExp : 0 ≤ freshExp)
    (hUniformity : ∀ step, step ∈ run.productLedger.steps →
      step.uniformityLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : ∀ step, step ∈ run.productLedger.steps →
      step.freshRetentionLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp))
    (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * U.coarseCard : Nat) : ENNReal))
    (firstCap : ENNReal) (lossEta : Real)
    (hGainedPrefix :
      R.collapsedPrefix (delta := delta) firstCap lossEta ≤
        (delta : ENNReal) ^ (10 * P.eta W.stage) *
          (coreNativeResidualFirstLoss run.productLedger X.thirdLoss *
            sectionEightScaleCountFrostmanFactor
              delta (canonicalBufferedRadius W) middleCount gamma))
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage)
    (hRawEq66 : Dsource.shading.averageMultiplicity ≤
      R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity)
    (hTauMiddle : Sseq.tau W.m ≤ canonicalBufferedRadius W)
    (hGammaOne : gamma ≤ 1)
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hGammaTwo : gamma ≤ 2 := hGammaOne.trans (by norm_num)
  let Z : NormalizedLongCoreActualPrefixEq66Inputs
      Dsource hDsource Cmulti Sseq P W :=
    groundedRun_normalizedActualPrefixEq66InputsOfCoreNativeGainedPrefix
      Dsource hDsource Cmulti sourceDef212Constant sourceExact Sseq P W X run
        hUniformityExp hFreshExp hUniformity hFresh middleCount
        (by
          simpa only [CoreNativeFrozenThirdBundle.thirdCount,
            Fintype.card_fin] using final_cardProduct_eq)
        (R.collapsedPrefix (delta := delta) firstCap lossEta)
          hGainedPrefix hGammaTwo hExponentBudget
  have hTriple : Dsource.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
    apply hTriple_of_rawEq66_coreNativeThird_gainedActualPrefix
      Dsource hDsource Cmulti Sseq P W Z X
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hRawEq66
  exact Z.toDividingScaleOutput Dsource hDsource Cmulti Sseq P W
    hTauMiddle hGammaOne hTriple hSmall hTargetEpsilon

#print axioms gainedActualPrefix
#print axioms coreNativeResidualFirstLoss
#print axioms coreNativeResidualFirst_mul_third_le_reverse
#print axioms gainedActualPrefix_le_of_raw_le_gain_mul
#print axioms
  groundedRun_normalizedActualPrefixEq66InputsOfCoreNativeGainedPrefix
#print axioms hTriple_of_rawEq66_coreNativeThird_gainedActualPrefix
#print axioms
  dividingScaleOutput_of_sameAssembly_coreNativeThird_gainedActualPrefix

end
end Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1

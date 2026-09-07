import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66InputsV1
import Family8Grounding.Family8OuterCountAggregatePowerBudgetV2
import Family8Grounding.Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
import Mathlib.Tactic

/-!
# Repeated bad-parent ledger to the correlated Equation (66) fields

The repeated bad-parent ledger already contains the two literal cardinality
products and the exact accumulated radius defect.  This file connects those
quantities to the two scalar fields required by
`NormalizedLongCoreCorrelatedEq66Inputs`:

* `hCount` is obtained from the ledger's forward cardinality theorem;
* `hAggregateLoss` is obtained from the literal forward/reverse loss products,
  the ledger's exact radius identity, and the existing outer/count power
  algebra.

The ledger does not bound its arbitrary one-step losses by a power of the
source scale.  Accordingly the two cumulative power envelopes remain named
inputs.  They are stated at the ledger-reconstructed source radius, rather
than directly at `delta`; the exact ledger radius theorem and the explicit
same-scale identification perform that transport here.  Likewise, the
source/final factor-cardinality identifications are explicit and inspectable.
No desired `hCount` or `hAggregateLoss` conclusion is accepted as an input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8OuterCountAggregatePowerBudgetV2
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1.RepeatedBadParentLedger
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## Literal cumulative ledger scalars -/

/-- The source radius reconstructed from the final factor list and the exact
fixed `64/3` defect accumulated at every bad-parent replacement. -/
def reconstructedSourceRadius
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) : NNReal :=
  (64 / 3 : NNReal) ^ ledger.steps.length *
    factorRadiusProduct finalFactors

/-- The literal product of all forward uniformity losses. -/
def cumulativeForwardLoss
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) : ENNReal :=
  (ledger.steps.map (fun step => step.uniformityLoss)).prod

/-- The literal product of every honest reverse loss `C_j * L_j`. -/
def cumulativeReverseLoss
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) : ENNReal :=
  (ledger.steps.map (fun step =>
    step.uniformityLoss * step.freshRetentionLoss)).prod

/-! ## Same-object identifications at the consumer seam -/

/-- The explicit object identifications needed to regard one literal factor
ledger as the middle/third count decomposition used by the correlated Eq. 66
consumer.

The outer-loss comparison is one-sided on purpose: unrelated already-paid
outer losses may be smaller than the full reverse ledger loss. -/
structure CorrelatedEq66LedgerIdentification
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (delta : NNReal) (index : Type) [Fintype index]
    (middleCount thirdCount : Nat)
    (firstLoss thirdLoss countLoss : ENNReal) : Prop where
  source_cardProduct_eq :
    factorCardProduct sourceFactors =
      (Fintype.card index : ENNReal)
  final_cardProduct_eq :
    factorCardProduct finalFactors =
      ((middleCount * thirdCount : Nat) : ENNReal)
  source_radiusProduct_eq_delta :
    factorRadiusProduct sourceFactors = delta
  countLoss_eq_forward :
    countLoss = cumulativeForwardLoss ledger
  outerLoss_le_reverse :
    firstLoss * thirdLoss <= cumulativeReverseLoss ledger

/-! ## Actual `hCount` and `hAggregateLoss` producer -/

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Produce exactly the `hCount` and `hAggregateLoss` fields of
`NormalizedLongCoreCorrelatedEq66Inputs` from a repeated bad-parent ledger.

The two power envelopes are the genuinely missing analytic estimates: the
ledger permits arbitrary `ENNReal` one-step losses and therefore cannot
manufacture them.  Their base is the reconstructed ledger radius, so the
conversion to the consumer's `delta` base necessarily uses the accumulated
radius theorem. -/
theorem count_and_aggregate_fields_of_repeatedBadParentLedger
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (middleCount thirdCount : Nat)
    (firstLoss thirdLoss countLoss : ENNReal)
    (I : CorrelatedEq66LedgerIdentification ledger delta index
      middleCount thirdCount firstLoss thirdLoss countLoss)
    {outerExponent countExponent : Real}
    (hgammaTwo : gamma <= 2)
    (hForwardPower :
      cumulativeForwardLoss ledger <=
        ((reconstructedSourceRadius ledger : NNReal) : ENNReal) ^
          (-countExponent))
    (hReversePower :
      cumulativeReverseLoss ledger <=
        ((reconstructedSourceRadius ledger : NNReal) : ENNReal) ^
          (-outerExponent))
    (hExponentBudget :
      outerExponent + countExponent * (1 - gamma / 2) <=
        3 * P.eta W.stage) :
    (((middleCount * thirdCount : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal)) /\
      (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
  obtain ⟨hRadiusRaw, hForwardRaw, _hReverseRaw⟩ :=
    ledger.cumulative_exactProductCertificate
  have hRadius :
      factorRadiusProduct sourceFactors =
        reconstructedSourceRadius ledger := by
    simpa only [reconstructedSourceRadius] using hRadiusRaw
  have hForward :
      factorCardProduct finalFactors <=
        cumulativeForwardLoss ledger *
          factorCardProduct sourceFactors := by
    simpa only [cumulativeForwardLoss] using hForwardRaw
  have hReconstructedSource :
      reconstructedSourceRadius ledger = delta := by
    calc
      reconstructedSourceRadius ledger =
          factorRadiusProduct sourceFactors := hRadius.symm
      _ = delta := I.source_radiusProduct_eq_delta
  have hCount :
      ((middleCount * thirdCount : Nat) : ENNReal) <=
        countLoss * (Fintype.card index : ENNReal) := by
    calc
      ((middleCount * thirdCount : Nat) : ENNReal) =
          factorCardProduct finalFactors := I.final_cardProduct_eq.symm
      _ <= cumulativeForwardLoss ledger *
          factorCardProduct sourceFactors := hForward
      _ = countLoss * (Fintype.card index : ENNReal) := by
        rw [<- I.countLoss_eq_forward, I.source_cardProduct_eq]
  have hForwardDeltaPower :
      cumulativeForwardLoss ledger <=
        (delta : ENNReal) ^ (-countExponent) := by
    calc
      cumulativeForwardLoss ledger <=
          ((reconstructedSourceRadius ledger : NNReal) : ENNReal) ^
            (-countExponent) := hForwardPower
      _ = (delta : ENNReal) ^ (-countExponent) := by
        rw [hReconstructedSource]
  have hReverseDeltaPower :
      cumulativeReverseLoss ledger <=
        (delta : ENNReal) ^ (-outerExponent) := by
    calc
      cumulativeReverseLoss ledger <=
          ((reconstructedSourceRadius ledger : NNReal) : ENNReal) ^
            (-outerExponent) := hReversePower
      _ = (delta : ENNReal) ^ (-outerExponent) := by
        rw [hReconstructedSource]
  have hCountLossPower :
      countLoss <= (delta : ENNReal) ^ (-countExponent) := by
    calc
      countLoss = cumulativeForwardLoss ledger := I.countLoss_eq_forward
      _ <= (delta : ENNReal) ^ (-countExponent) := hForwardDeltaPower
  have hOuterLossPower :
      firstLoss * thirdLoss <=
        (delta : ENNReal) ^ (-outerExponent) :=
    I.outerLoss_le_reverse.trans hReverseDeltaPower
  have hdeltaOne : delta <= 1 := by
    exact hD.delta_le_half.trans (by norm_num)
  have hExponentBudget' :
      outerExponent + 0 + countExponent * (1 - gamma / 2) <=
        3 * P.eta W.stage := by
    simpa only [add_zero] using hExponentBudget
  have hAggregateRaw :=
    outerCountAggregateLoss_le_threeEta
      (delta := delta)
      (firstLoss := firstLoss * thirdLoss)
      (thirdLoss := (1 : ENNReal))
      (countLoss := countLoss)
      (firstExponent := outerExponent)
      (thirdExponent := 0)
      (countExponent := countExponent)
      (eta := P.eta W.stage) (gamma := gamma)
      hD.delta_pos hdeltaOne hgammaTwo hOuterLossPower
        (by norm_num) hCountLossPower hExponentBudget'
  refine ⟨hCount, ?_⟩
  simpa only [mul_one] using hAggregateRaw

#print axioms CorrelatedEq66LedgerIdentification
#print axioms count_and_aggregate_fields_of_repeatedBadParentLedger

end
end Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1

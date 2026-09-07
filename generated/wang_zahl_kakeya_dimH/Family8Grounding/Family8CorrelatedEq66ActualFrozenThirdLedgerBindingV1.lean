import Family8Grounding.Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
import Mathlib.Tactic

/-!
# Actual frozen-third allocation of the correlated Equation (66) ledger

The repeated bad-parent ledger carries one literal cumulative reverse loss.
The terminal Equation-(66) consumer, however, names two factors
`firstLoss * thirdLoss` and separately asks that the selected frozen average
be at most `thirdLoss`.

This module makes that split canonically on the same frozen assembly:

* `thirdLoss` is the actual frozen-coarse average multiplicity;
* `firstLoss` is the residual quotient of the cumulative reverse loss by
  that actual average;
* `countLoss` is the literal cumulative forward loss.

The required one-sided reverse-loss domination is then the unconditional
`ENNReal.mul_div_le`; no scalar equality or per-step identification is
assumed.  At the final-state seam we retain only the cardinality-product
equality consumed by the existing ledger connector, without identifying or
reindexing the heterogeneous factor list itself.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex fineIndex coarseIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  [Fintype fineIndex] [DecidableEq fineIndex]
  [Fintype coarseIndex] [DecidableEq coarseIndex]
  {scale rho : NNReal}
  {fine : UniformTubeFamily scale fineIndex}
  {G : ConvexFamily coarseIndex}

/-- The terminal loss is the literal average of the same frozen assembly
used by the selected-third certificate and the raw Equation (66). -/
def actualFrozenThirdLedgerLoss
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1) : ENNReal :=
  A.frozenCoarse.averageMultiplicity

/-- The portion of the literal reverse ledger remaining after allocating
the actual frozen-third loss. -/
def residualFirstLedgerLoss
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1) : ENNReal :=
  cumulativeReverseLoss ledger / actualFrozenThirdLedgerLoss A

/-- The exact one-sided domination required by
`CorrelatedEq66LedgerIdentification`.  It is valid even at zero or infinity,
so no hidden positivity or finiteness premise is introduced. -/
theorem residualFirst_mul_actualFrozenThird_le_reverse
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1) :
    residualFirstLedgerLoss ledger A * actualFrozenThirdLedgerLoss A <=
      cumulativeReverseLoss ledger := by
  rw [residualFirstLedgerLoss, mul_comm]
  exact ENNReal.mul_div_le

/-- The actual frozen average satisfies the terminal third-loss allocation
definitionally. -/
theorem actualFrozenAverage_le_actualFrozenThirdLedgerLoss
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1) :
    A.frozenCoarse.averageMultiplicity <= actualFrozenThirdLedgerLoss A := by
  exact le_rfl

/-- Canonical correlated-ledger identification for a grounded run starting
at the full-refinement singleton state.

There are no free `firstLoss`, `thirdLoss`, `countLoss`, or reverse-loss
comparison arguments.  The sole final-state provenance input is precisely
the cardinality-product equality used by the consumer. -/
theorem groundedRun_correlatedEq66LedgerIdentification_actualFrozenThird
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base sourceDef212Constant)
    {Y : Shading fine.bodyFamily}
    {Q : ConvexFactorization fine.bodyFamily G}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    {runN sourceStage finalStage : Nat}
    {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource Cmulti sourceDef212Constant sourceExact) finalState)
    (middleCount : Nat)
    (final_cardProduct_eq :
      factorCardProduct finalState.factors =
        ((middleCount * Fintype.card coarseIndex : Nat) : ENNReal)) :
    CorrelatedEq66LedgerIdentification run.productLedger delta sourceIndex
      middleCount (Fintype.card coarseIndex)
      (residualFirstLedgerLoss run.productLedger A)
      (actualFrozenThirdLedgerLoss A)
      (cumulativeForwardLoss run.productLedger) := by
  exact
    groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
      Dsource hDsource Cmulti sourceDef212Constant sourceExact run
      middleCount (Fintype.card coarseIndex)
      (residualFirstLedgerLoss run.productLedger A)
      (actualFrozenThirdLedgerLoss A) final_cardProduct_eq
      (residualFirst_mul_actualFrozenThird_le_reverse run.productLedger A)

#print axioms actualFrozenThirdLedgerLoss
#print axioms residualFirstLedgerLoss
#print axioms residualFirst_mul_actualFrozenThird_le_reverse
#print axioms actualFrozenAverage_le_actualFrozenThirdLedgerLoss
#print axioms
  groundedRun_correlatedEq66LedgerIdentification_actualFrozenThird

end
end Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1

import Family8Grounding.Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
import Mathlib.Tactic

/-!
# Literal singleton source provenance for the correlated Equation (66) ledger

The source cardinality and radius of a repeated paper-factor ledger are
definitionally determined when its source list is the singleton containing
`ActualFactorDatum.ofDatum Dsource`.  This module packages that observation
without manufacturing any hierarchy or selecting a replacement object.

At the factor-list level, only the final cardinality decomposition and the
outer-loss comparison remain inputs.  To form an actual `PaperFactorState`,
the exact source atom still needs its genuine coherent cover and Exact
Definition 2.12 certificate; these are exposed explicitly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8CorrelatedEq66LiteralSingletonSourceProvenanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The literal source atom used to initialize the factor ledger. -/
def correlatedEq66LiteralSourceFactor
    (Dsource : ActualTubeDatum delta index) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum Dsource

/-- The canonical singleton source factor list. -/
def correlatedEq66LiteralSourceFactors
    (Dsource : ActualTubeDatum delta index) : List ActualFactorDatum :=
  [correlatedEq66LiteralSourceFactor Dsource]

@[simp]
theorem correlatedEq66LiteralSourceFactors_cardProduct
    (Dsource : ActualTubeDatum delta index) :
    factorCardProduct (correlatedEq66LiteralSourceFactors Dsource) =
      (Fintype.card index : ENNReal) := by
  simp only [correlatedEq66LiteralSourceFactors,
    correlatedEq66LiteralSourceFactor, factorCardProduct_cons,
    ActualFactorDatum.ofDatum_card, factorCardProduct_nil, mul_one]

@[simp]
theorem correlatedEq66LiteralSourceFactors_radiusProduct
    (Dsource : ActualTubeDatum delta index) :
    factorRadiusProduct (correlatedEq66LiteralSourceFactors Dsource) =
      delta := by
  simp only [correlatedEq66LiteralSourceFactors,
    correlatedEq66LiteralSourceFactor, factorRadiusProduct_cons,
    ActualFactorDatum.ofDatum_radius, factorRadiusProduct_nil, mul_one]

/-- Package the exact source readiness once its genuine hierarchy and Exact
Definition 2.12 certificate have been supplied. -/
def correlatedEq66LiteralSourceReadiness
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Csource : CoherentStickyMultiscaleCover Dsource.family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Csource.base def212Constant) :
    PaperFactorAtomReadiness
      (correlatedEq66LiteralSourceFactor Dsource) where
  admissible := hDsource
  coherentCover := Csource
  def212Constant := def212Constant
  exactDef212 := sourceExact

/-- The canonical singleton source paper state.  Unlike the factor list, this
object necessarily consumes real recursive readiness for the source atom. -/
def correlatedEq66LiteralSingletonSourceState
    (Dsource : ActualTubeDatum delta index)
    (sourceReadiness : PaperFactorAtomReadiness
      (correlatedEq66LiteralSourceFactor Dsource)) : PaperFactorState :=
  PaperFactorState.ofFactors
    (correlatedEq66LiteralSourceFactors Dsource)
    (.cons sourceReadiness .nil)

@[simp]
theorem correlatedEq66LiteralSingletonSourceState_factors
    (Dsource : ActualTubeDatum delta index)
    (sourceReadiness : PaperFactorAtomReadiness
      (correlatedEq66LiteralSourceFactor Dsource)) :
    (correlatedEq66LiteralSingletonSourceState
      Dsource sourceReadiness).factors =
        correlatedEq66LiteralSourceFactors Dsource :=
  rfl

/-- At a literally singleton source list, the three source-side Eq. 66
identifications are definitional.  Only the final count decomposition and
outer-loss comparison are genuine remaining seams. -/
theorem correlatedEq66LedgerIdentification_of_literalSingletonSource
    (Dsource : ActualTubeDatum delta index)
    {finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger
      (correlatedEq66LiteralSourceFactors Dsource) finalFactors)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalFactors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss ledger) :
    CorrelatedEq66LedgerIdentification ledger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss ledger) where
  source_cardProduct_eq :=
    correlatedEq66LiteralSourceFactors_cardProduct Dsource
  final_cardProduct_eq := final_cardProduct_eq
  source_radiusProduct_eq_delta :=
    correlatedEq66LiteralSourceFactors_radiusProduct Dsource
  countLoss_eq_forward := rfl
  outerLoss_le_reverse := outerLoss_le_reverse

/-- The same producer for an existing ledger whose source-factor provenance
has already been identified with the literal singleton.  This form applies
directly to an existing grounded run. -/
theorem correlatedEq66LedgerIdentification_of_sourceFactors_eq_literalSingleton
    (Dsource : ActualTubeDatum delta index)
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (sourceFactors_eq :
      sourceFactors = correlatedEq66LiteralSourceFactors Dsource)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalFactors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss ledger) :
    CorrelatedEq66LedgerIdentification ledger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss ledger) where
  source_cardProduct_eq := by
    rw [sourceFactors_eq]
    exact correlatedEq66LiteralSourceFactors_cardProduct Dsource
  final_cardProduct_eq := final_cardProduct_eq
  source_radiusProduct_eq_delta := by
    rw [sourceFactors_eq]
    exact correlatedEq66LiteralSourceFactors_radiusProduct Dsource
  countLoss_eq_forward := rfl
  outerLoss_le_reverse := outerLoss_le_reverse

/-- Produce the exact identification expected by
`groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh` from an arbitrary
grounded run once its source factors are known to be the literal singleton.
The consumer should instantiate `countLoss` with the displayed cumulative
forward loss. -/
theorem groundedRun_correlatedEq66LedgerIdentification_of_sourceFactors_eq
    (Dsource : ActualTubeDatum delta index)
    {runN sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      sourceState finalState)
    (sourceFactors_eq : sourceState.factors =
      correlatedEq66LiteralSourceFactors Dsource)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalState.factors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss run.productLedger) :
    CorrelatedEq66LedgerIdentification run.productLedger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss run.productLedger) :=
  correlatedEq66LedgerIdentification_of_sourceFactors_eq_literalSingleton
    Dsource run.productLedger sourceFactors_eq middleCount thirdCount
      firstLoss thirdLoss final_cardProduct_eq outerLoss_le_reverse

/-- When the grounded run is indexed by the canonical singleton state, even
the source-factor equality disappears.  The only inputs left are the final
factor-cardinality decomposition and outer-loss comparison. -/
theorem groundedRun_correlatedEq66LedgerIdentification_of_literalSingletonState
    (Dsource : ActualTubeDatum delta index)
    (sourceReadiness : PaperFactorAtomReadiness
      (correlatedEq66LiteralSourceFactor Dsource))
    {runN sourceStage finalStage : Nat}
    {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66LiteralSingletonSourceState
        Dsource sourceReadiness) finalState)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalState.factors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss run.productLedger) :
    CorrelatedEq66LedgerIdentification run.productLedger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss run.productLedger) :=
  groundedRun_correlatedEq66LedgerIdentification_of_sourceFactors_eq
    Dsource run rfl middleCount thirdCount firstLoss thirdLoss
      final_cardProduct_eq outerLoss_le_reverse

#print axioms correlatedEq66LiteralSourceFactor
#print axioms correlatedEq66LiteralSourceFactors
#print axioms correlatedEq66LiteralSourceFactors_cardProduct
#print axioms correlatedEq66LiteralSourceFactors_radiusProduct
#print axioms correlatedEq66LiteralSourceReadiness
#print axioms correlatedEq66LiteralSingletonSourceState
#print axioms correlatedEq66LiteralSingletonSourceState_factors
#print axioms correlatedEq66LedgerIdentification_of_literalSingletonSource
#print axioms
  correlatedEq66LedgerIdentification_of_sourceFactors_eq_literalSingleton
#print axioms
  groundedRun_correlatedEq66LedgerIdentification_of_sourceFactors_eq
#print axioms
  groundedRun_correlatedEq66LedgerIdentification_of_literalSingletonState

end
end Family8CorrelatedEq66LiteralSingletonSourceProvenanceV1

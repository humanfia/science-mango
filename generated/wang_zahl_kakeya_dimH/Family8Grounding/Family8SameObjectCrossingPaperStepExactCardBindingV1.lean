import Family8Grounding.Family8PaperFactorFiniteRunV2
import Mathlib.Tactic

/-!
# Exact factor-card binding for one same-object crossing step

`SameObjectCrossingPaperStep` already stores the literal paper transition
built from its integrated successor.  This module exposes the two endpoint
cardinality products without choosing another cover, parent, or selected
subtype.  In particular, the successor product uses the exact
`dualChild.qFibreState.base.selected` occurring in the step.

These identities expose why a naked final-card product is not a faithful
description of a run step: both surrounding products remain.  They do not
bind an independently selected canonical graph/proxy subset to the q-fresh
subset.  In particular, no external equality between those selections is
requested or suggested here.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal NNReal

namespace Family8SameObjectCrossingPaperStepExactCardBindingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}

/-- Exact source cardinality product of the paper step, with the selected
active-fine factor displayed in its literal surrounding list. -/
theorem sameObjectCrossingPaperStep_source_cardProduct
    (step : SameObjectCrossingPaperStep W) :
    factorCardProduct step.paperTransition.source.factors =
      factorCardProduct step.integrated.readiness.left *
        ((crossingBaseCover W).activeFine.card : ENNReal) *
          factorCardProduct step.integrated.readiness.right := by
  calc
    factorCardProduct step.paperTransition.source.factors =
        factorCardProduct
          step.integrated.dualChild.qFibreState.sourceFactors :=
      congrArg factorCardProduct step.paperTransition.source_factors_eq
    _ = factorCardProduct step.integrated.readiness.left *
          ((crossingBaseCover W).activeFine.card : ENNReal) *
            factorCardProduct step.integrated.readiness.right := by
      simp only [Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState.sourceFactors,
        badParentSourceFactorList, factorCardProduct_append,
        factorCardProduct_cons, badParentActiveFineSourceAtom_card]
      ac_rfl

/-- Exact successor cardinality product of the same paper step.  The fresh
factor is definitionally indexed by the very selected subtype stored by the
integrated successor; no cardinality comparison or re-selection is used. -/
theorem sameObjectCrossingPaperStep_successor_cardProduct
    (step : SameObjectCrossingPaperStep W) :
    factorCardProduct step.paperTransition.successor.factors =
      factorCardProduct step.integrated.readiness.left *
        (((crossingBaseCover W).activeCoarse.card *
            step.integrated.dualChild.qFibreState.base.selected.card : Nat) :
          ENNReal) *
          factorCardProduct step.integrated.readiness.right := by
  calc
    factorCardProduct step.paperTransition.successor.factors =
        factorCardProduct
          step.integrated.dualChild.qFibreState.successorFactors :=
      congrArg factorCardProduct step.paperTransition.successor_factors_eq
    _ = factorCardProduct step.integrated.readiness.left *
          (((crossingBaseCover W).activeCoarse.card *
              step.integrated.dualChild.qFibreState.base.selected.card : Nat) :
            ENNReal) *
            factorCardProduct step.integrated.readiness.right := by
      simp only [Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState.successorFactors,
        badParentSuccessorFactorList, factorCardProduct_append,
        factorCardProduct_cons, badParentCoarseAtom_card,
        badParentFreshChildAtom_card, Nat.cast_mul]
      ac_rfl

#print axioms sameObjectCrossingPaperStep_source_cardProduct
#print axioms sameObjectCrossingPaperStep_successor_cardProduct

end
end Family8SameObjectCrossingPaperStepExactCardBindingV1

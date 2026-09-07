import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
import Family8Grounding.Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1
import Mathlib.Tactic

/-!
# Selection-first actual-ledger consumer from a retained-source budget

The selection-first actual-ledger context asks for the displayed coefficient
to be bounded by the average multiplicity of the canonical graph selected by
the same `R`.  The retained-source calibration proves precisely that input from one
division-free scalar budget and a transported source-density retention bound.

This file is deliberately a continuation-style consumer.  It neither selects
a graph nor claims that the scalar budget is automatic.  Thus the only new
analytic seam exposed here is the literal `hBudget`; all witness-bearing data
remain fixed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenActualLedgerSelectionFirstRetainedSourceBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenRetainedSourceDensityCalibrationV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho delta : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- Replace the selection-first actual-ledger input
`displayed <= R.graphAverage` by the weakest retained-source density budget.

`consume` can be the remainder of the existing
`SameAssemblyGraphFrozenActualLedgerDSOClosure` after all arguments preceding
`hDisplayedToGraph` have been fixed.  No graph, assembly, label, source
density, or loss is changed by this adapter.  In a generic caller,
`hSourceDensity` still has to be transported to the literal active-fine
density appearing below; only a specialized context may treat it as already
available. -/
theorem consume_actualLedgerContext_of_retainedSourceDensityBudget
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau)
    (X selectorLoss sourceDensity densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (hSourceDensity : densityRetentionLoss * sourceDensity <=
      (sourceActiveFineShading P Y).shadingDensity)
    (hBudget :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
          (((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal)) * R.graphLoss) <=
        densityRetentionLoss * sourceDensity)
    (Goal : Prop)
    (consume :
      (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage) -> Goal) :
    Goal := by
  apply consume
  exact actualLedgerClosure_displayedInput_of_retainedSourceDensityBudget
    R htau X selectorLoss sourceDensity densityRetentionLoss outputEta
      hSourceDensity hBudget

#print axioms
  consume_actualLedgerContext_of_retainedSourceDensityBudget

end

end Family8CanonicalGraphFrozenActualLedgerSelectionFirstRetainedSourceBudgetV1

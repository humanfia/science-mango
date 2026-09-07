import Family8Grounding.Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1
import Mathlib.Tactic

/-!
# Exact ledger criterion for the gained-prefix first-scale payment

The gained-prefix composer assigns the reverse-ledger residual

`cumulativeReverseLoss / thirdLoss`

to the first scale.  For a finite positive `thirdLoss`, its remaining
first-scale hypothesis is *equivalent* to the quotient-free inequality

`thirdLoss <= cumulativeReverseLoss * firstScaleFactor`.

This file records that equivalence and one count-ledger sufficient
criterion.  In particular, it does not claim that the Section-8 singleton
factor or the reverse ledger automatically supplies the lower bound.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenCoreNativeResidualFirstScaleLedgerBridgeV1

open Submission.Kakeya.ConvexFactoring
open Family8CanonicalGraphFrozenCoreNativeThirdGainedActualPrefixToDSOV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1.RepeatedBadParentLedger
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1

noncomputable section

/-! ## Exact quotient-free form -/

/-- For a finite positive denominator, the gained-prefix lower bound is
exactly the corresponding quotient-free product comparison. -/
theorem one_le_div_mul_iff
    {reverseLoss thirdLoss firstScaleFactor : ENNReal}
    (hthird0 : thirdLoss ≠ 0) (hthirdTop : thirdLoss ≠ ∞) :
    1 <= (reverseLoss / thirdLoss) * firstScaleFactor <->
      thirdLoss <= reverseLoss * firstScaleFactor := by
  have hreorder :
      (reverseLoss / thirdLoss) * firstScaleFactor =
        (reverseLoss * firstScaleFactor) / thirdLoss := by
    simp only [div_eq_mul_inv]
    ac_rfl
  rw [hreorder]
  simpa only [one_mul] using
    (ENNReal.le_div_iff_mul_le
      (a := (1 : ENNReal)) (b := thirdLoss)
      (c := reverseLoss * firstScaleFactor)
      (Or.inl hthird0) (Or.inl hthirdTop))

/-- Exact quotient-free characterization for the residual allocation used
by the Core-native gained-prefix composer. -/
theorem coreNativeResidualFirst_mul_factor_iff
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {thirdLoss firstScaleFactor : ENNReal}
    (hthird0 : thirdLoss ≠ 0) (hthirdTop : thirdLoss ≠ ∞) :
    1 <= coreNativeResidualFirstLoss ledger thirdLoss * firstScaleFactor <->
      thirdLoss <= cumulativeReverseLoss ledger * firstScaleFactor := by
  exact one_le_div_mul_iff hthird0 hthirdTop

/-- Direct sufficient form of the exact quotient-free criterion. -/
theorem coreNativeResidualFirst_mul_factor_ge_one
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {thirdLoss firstScaleFactor : ENNReal}
    (hthird0 : thirdLoss ≠ 0) (hthirdTop : thirdLoss ≠ ∞)
    (hbudget : thirdLoss <=
      cumulativeReverseLoss ledger * firstScaleFactor) :
    1 <= coreNativeResidualFirstLoss ledger thirdLoss * firstScaleFactor :=
  (coreNativeResidualFirst_mul_factor_iff
    ledger hthird0 hthirdTop).2 hbudget

/-! ## Honest count-ledger sufficient criterion -/

/-- The reverse cardinality certificate converts a count-normalized
third-loss budget into the exact quotient-free first-scale budget.

The displayed `hcountBudget` is intentionally retained: the ledger supplies
only the comparison between source and final cardinality products, not this
analytic third-loss/scale comparison. -/
theorem thirdLoss_le_reverse_mul_factor_of_countBudget
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {thirdLoss firstScaleFactor : ENNReal}
    (hfinal0 : factorCardProduct finalFactors ≠ 0)
    (hfinalTop : factorCardProduct finalFactors ≠ ∞)
    (hcountBudget :
      thirdLoss * factorCardProduct finalFactors <=
        factorCardProduct sourceFactors * firstScaleFactor) :
    thirdLoss <= cumulativeReverseLoss ledger * firstScaleFactor := by
  have hreverse : factorCardProduct sourceFactors <=
      cumulativeReverseLoss ledger * factorCardProduct finalFactors := by
    simpa only [cumulativeReverseLoss] using
      ledger.source_cardProduct_le_list_prod_mul_final
  apply (ENNReal.mul_le_mul_iff_left hfinal0 hfinalTop).1
  calc
    thirdLoss * factorCardProduct finalFactors <=
        factorCardProduct sourceFactors * firstScaleFactor := hcountBudget
    _ <= (cumulativeReverseLoss ledger *
          factorCardProduct finalFactors) * firstScaleFactor :=
      mul_le_mul' hreverse le_rfl
    _ = (cumulativeReverseLoss ledger * firstScaleFactor) *
          factorCardProduct finalFactors := by ac_rfl

/-- Count-normalized sufficient producer for the gained-prefix first-scale
hypothesis.  This makes precise the additional estimate that would have to
be grounded in the selected third bundle and the literal factor ledger. -/
theorem coreNativeResidualFirst_mul_factor_ge_one_of_countBudget
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    {thirdLoss firstScaleFactor : ENNReal}
    (hthird0 : thirdLoss ≠ 0) (hthirdTop : thirdLoss ≠ ∞)
    (hfinal0 : factorCardProduct finalFactors ≠ 0)
    (hfinalTop : factorCardProduct finalFactors ≠ ∞)
    (hcountBudget :
      thirdLoss * factorCardProduct finalFactors <=
        factorCardProduct sourceFactors * firstScaleFactor) :
    1 <= coreNativeResidualFirstLoss ledger thirdLoss * firstScaleFactor := by
  apply coreNativeResidualFirst_mul_factor_ge_one
    ledger hthird0 hthirdTop
  exact thirdLoss_le_reverse_mul_factor_of_countBudget
    ledger hfinal0 hfinalTop hcountBudget

#print axioms one_le_div_mul_iff
#print axioms coreNativeResidualFirst_mul_factor_iff
#print axioms coreNativeResidualFirst_mul_factor_ge_one
#print axioms thirdLoss_le_reverse_mul_factor_of_countBudget
#print axioms coreNativeResidualFirst_mul_factor_ge_one_of_countBudget

end
end Family8CanonicalGraphFrozenCoreNativeResidualFirstScaleLedgerBridgeV1

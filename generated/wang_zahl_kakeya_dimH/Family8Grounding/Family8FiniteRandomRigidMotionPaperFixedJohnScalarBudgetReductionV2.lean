import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2

noncomputable section

/-!
# Scalar budgets after removing the automatic repetition count

The fixed-John Frostman connector displays two scalar premises.  This module
puts the density premise in its honest cross-multiplied form and proves that
the automatic positive repetition count cancels completely from the
unit-ball base premise.  Thus the remaining base dichotomy is a source-card
budget, not a random-choice or repetition callback.
-/

/-- The greedy loss is a positive finite denominator. -/
theorem fixedJohnAutomaticGreedyLoss_ne_zero
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ≠ 0 := by
  exact_mod_cast
    (show fixedJohnAutomaticGreedyLoss D hD ≠ 0 by
      unfold fixedJohnAutomaticGreedyLoss
      omega)

/-- Cross-multiplication is a sufficient, division-free density budget. -/
theorem fixedJohnDensityBudget_of_cross
    {eta : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcross :
      ((delta / 8 : NNReal) : ENNReal) ^ eta *
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ≤
        (eighthNormalizedDatum D).shading.shadingDensity) :
    ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
      (eighthNormalizedDatum D).shading.shadingDensity /
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) := by
  exact
    (ENNReal.le_div_iff_mul_le
      (Or.inl (fixedJohnAutomaticGreedyLoss_ne_zero D hD))
      (Or.inl ENNReal.coe_ne_top)).2 hcross

/-- The exact unit-ball base budget no longer depends on the automatically
chosen repetition count: multiplying a one-copy source-card budget by that
positive integer gives the product-family budget. -/
theorem fixedJohnBaseBudget_of_reduced
    {eta : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal)
    (hreduced :
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 *
              ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := by
  let J := fixedJohnAutomaticDensityRepetitions D hD
  calc
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 * ((J : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) =
        (J : ENNReal) *
          ((fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
            ((128 * C) * volume (unitBallBody : Set Space))) := by
      ac_rfl
    _ ≤ (J : ENNReal) *
        (((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :=
      mul_le_mul' le_rfl hreduced
    _ = ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card (Fin J × iota) : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ac_rfl

/-- Both exact connector premises follow from the division-free density
budget and the repetition-free source-card base budget. -/
theorem fixedJohnScalarBudgets_of_reduced
    {eta : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal)
    (hdensity :
      ((delta / 8 : NNReal) : ENNReal) ^ eta *
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ≤
        (eighthNormalizedDatum D).shading.shadingDensity)
    (hbase :
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
        (eighthNormalizedDatum D).shading.shadingDensity /
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ∧
      (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((128 *
              ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) :
                ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) :=
  ⟨fixedJohnDensityBudget_of_cross D hD hdensity,
    fixedJohnBaseBudget_of_reduced D hD C hbase⟩

#print axioms fixedJohnAutomaticGreedyLoss_ne_zero
#print axioms fixedJohnDensityBudget_of_cross
#print axioms fixedJohnBaseBudget_of_reduced
#print axioms fixedJohnScalarBudgets_of_reduced

end
end Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2

import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyFrostmanCWAV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyBudgetReductionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionRelativeCanonicalCardAutomaticCopyCountV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyRefinementCWAV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Scalar budgets after fixing the canonical scale-only copy count

The sharp bound `J ≤ 2 * C_can` removes the integer copy count from both
product-mean scale conditions.  The same positive copy factor cancels exactly
from the Frostman unit-ball base budget.  These are algebraic reductions only;
the resulting source-level inequalities remain substantive premises.
-/

/-- The greedy loss after inserting the canonical conflict tail. -/
def scaleOnlyCanonicalCopyGreedyLoss
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal) : Nat :=
  scaleOnlyJointGreedyLoss
    (scaleOnlyJointConflictTailParameter D hD.delta_pos) (128 * C)

/-- The canonical copy-count John scale budget follows from its source-level
factor-two relaxation. -/
theorem scaleOnlyCanonicalCopy_johnScale_of_reduced
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hcanonical0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ 0)
    (hcanonicalTop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ ∞)
    (C : ENNReal)
    (hreduced :
      (2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D)) *
          scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume) :
    (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume := by
  calc
    (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        (2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D)) *
          scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta := by
      gcongr
      exact copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
        D hcanonical0 hcanonicalTop
    _ ≤ (128 * C) * scaleOnlyJointMotionBallVolume := hreduced

/-- The canonical copy-count conflict scale budget follows from the analogous
source-level factor-two relaxation. -/
theorem scaleOnlyCanonicalCopy_conflictScale_of_reduced
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hcanonical0 :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ 0)
    (hcanonicalTop :
      sourceCanonicalFrostmanConstant (eighthNormalizedDatum D) ≠ ∞)
    (C : ENNReal)
    (hreduced :
      (2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D)) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume) :
    (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        (128 * C) * scaleOnlyJointMotionBallVolume := by
  calc
    (relativeCanonicalCardCopyCount D : ENNReal) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        (2 * sourceCanonicalFrostmanConstant (eighthNormalizedDatum D)) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta := by
      gcongr
      exact copyCount_le_two_mul_eighth_sourceCanonicalFrostmanConstant
        D hcanonical0 hcanonicalTop
    _ ≤ (128 * C) * scaleOnlyJointMotionBallVolume := hreduced

/-- The positive canonical copy count cancels from the exact product-family
Frostman base budget. -/
theorem scaleOnlyCanonicalCopy_baseBudget_of_reduced
    {eta : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal)
    (hreduced :
      (scaleOnlyCanonicalCopyGreedyLoss D hD C : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card iota : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    (scaleOnlyCanonicalCopyGreedyLoss D hD C : ENNReal) *
          ((128 *
              ((relativeCanonicalCardCopyCount D : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (relativeCanonicalCardCopyCount D) × iota) : ENNReal) *
            (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) := by
  let J := relativeCanonicalCardCopyCount D
  calc
    (scaleOnlyCanonicalCopyGreedyLoss D hD C : ENNReal) *
          ((128 * ((J : ENNReal) * C)) *
            volume (unitBallBody : Set Space)) =
        (J : ENNReal) *
          ((scaleOnlyCanonicalCopyGreedyLoss D hD C : ENNReal) *
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

#print axioms scaleOnlyCanonicalCopyGreedyLoss
#print axioms scaleOnlyCanonicalCopy_johnScale_of_reduced
#print axioms scaleOnlyCanonicalCopy_conflictScale_of_reduced
#print axioms scaleOnlyCanonicalCopy_baseBudget_of_reduced

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyAutomaticCopyBudgetReductionV1

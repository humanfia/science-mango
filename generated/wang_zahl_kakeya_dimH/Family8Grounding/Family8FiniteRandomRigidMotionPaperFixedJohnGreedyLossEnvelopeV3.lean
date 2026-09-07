import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossEnvelopeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnScalarBudgetReductionV2

noncomputable section

/-!
# Removing the ceiling from the fixed-John greedy loss

The literal greedy loss is one plus a ceiling.  The following envelope removes
that integer rounding exactly: it is at most the logarithmic tail times the
sum of the genuine fixed-John paper caps, plus two.  This is the starting
point for the subsequent polynomial catalogue and concentration bounds.
-/

/-- Real-valued ceiling-free upper bound for the automatic greedy loss. -/
theorem fixedJohnAutomaticGreedyLoss_cast_le_envelope
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnTailParameter D hD *
          ∑ K : FixedJohnTest D hD,
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K +
        2 := by
  let x : Real :=
    fixedJohnTailParameter D hD *
      ∑ K : FixedJohnTest D hD,
        fixedJohnTranslationPaperCap
          (fixedJohnPackingGridVector D hD) D hD K
  have htail : 0 ≤ fixedJohnTailParameter D hD :=
    (zero_le_one.trans (one_le_fixedJohnTailParameter D hD))
  have hsum : 0 ≤
      ∑ K : FixedJohnTest D hD,
        fixedJohnTranslationPaperCap
          (fixedJohnPackingGridVector D hD) D hD K := by
    exact Finset.sum_nonneg fun K _hK =>
      fixedJohnPaperCap_nonneg (fixedJohnPackingGridVector D hD) D hD K
  have hx : 0 ≤ x := mul_nonneg htail hsum
  have hceil : (fixedJohnLoadThreshold
      (fixedJohnPackingGridVector D hD) D hD : Real) < x + 1 := by
    simpa only [fixedJohnLoadThreshold, x] using
      Nat.ceil_lt_add_one hx
  unfold fixedJohnAutomaticGreedyLoss
  push_cast
  dsimp only [x] at hceil ⊢
  linarith

/-- ENNReal spelling of the same finite envelope. -/
theorem fixedJohnAutomaticGreedyLoss_le_envelope
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) ≤
      ENNReal.ofReal
        (fixedJohnTailParameter D hD *
            ∑ K : FixedJohnTest D hD,
              fixedJohnTranslationPaperCap
                (fixedJohnPackingGridVector D hD) D hD K +
          2) := by
  simpa only [ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal
      (fixedJohnAutomaticGreedyLoss_cast_le_envelope D hD)

/-- An envelope-level density estimate automatically supplies the exact
division-form density premise of the Frostman connector. -/
theorem fixedJohnDensityBudget_of_envelope
    {eta : Real} {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (henvelope :
      ((delta / 8 : NNReal) : ENNReal) ^ eta *
          ENNReal.ofReal
            (fixedJohnTailParameter D hD *
                ∑ K : FixedJohnTest D hD,
                  fixedJohnTranslationPaperCap
                    (fixedJohnPackingGridVector D hD) D hD K +
              2) ≤
        (eighthNormalizedDatum D).shading.shadingDensity) :
    ((delta / 8 : NNReal) : ENNReal) ^ eta ≤
      (eighthNormalizedDatum D).shading.shadingDensity /
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) := by
  apply fixedJohnDensityBudget_of_cross D hD
  exact (mul_le_mul' le_rfl
    (fixedJohnAutomaticGreedyLoss_le_envelope D hD)).trans henvelope

#print axioms fixedJohnAutomaticGreedyLoss_cast_le_envelope
#print axioms fixedJohnAutomaticGreedyLoss_le_envelope
#print axioms fixedJohnDensityBudget_of_envelope

end
end Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossEnvelopeV3

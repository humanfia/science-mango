import FamilyStickyGrounding.FamilyStickyDeltaMaxFiniteChainV2

open scoped ENNReal NNReal

namespace FamilyStickyTopScaleNormalizationV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Sticky Kakeya: honest top-scale normalization

The top value in the finite `Delta_max` chain is at most one when the top
family is literally a single indexed convex body.  This is the normalization
used at scale one in the source argument.  No claim is made for an arbitrary
radius-one indexed family: repetitions can make its concentration larger
than one.
-/

/-- A one-member indexed convex family. -/
def singletonConvexFamily (B : ConvexBody Space) : ConvexFamily (Fin 1) :=
  fun _ => B

/-- The concentration of one indexed convex body in every test body is at
most one, including the zero-volume case. -/
theorem concentration_singletonConvexFamily_le_one
    (B K : ConvexBody Space) :
    concentration (singletonConvexFamily B) K ≤ 1 := by
  unfold concentration singletonConvexFamily
  by_cases hBK : (B : Set Space) ⊆ (K : Set Space)
  · have hdiv :
        MeasureTheory.volume (B : Set Space) /
            MeasureTheory.volume (K : Set Space) ≤ (1 : ENNReal) := by
      apply ENNReal.div_le_of_le_mul
      simpa only [one_mul] using MeasureTheory.measure_mono hBK
    simpa [containedIndices, hBK] using hdiv
  · simp [containedIndices, hBK]

/-- Consequently the actual supremal concentration of the singleton family
is at most one. -/
theorem maximalConcentration_singletonConvexFamily_le_one
    (B : ConvexBody Space) :
    maximalConcentration (singletonConvexFamily B) ≤ 1 := by
  apply iSup_le
  exact concentration_singletonConvexFamily_le_one B

/-- Thin adapter for the last node of a finite chain.  The residual equality
is only the reindex/identification saying that the actual top family is the
singleton family; the numerical normalization is then automatic. -/
theorem top_le_one_of_eq_singleton
    {topDelta : ENNReal} (B : ConvexBody Space)
    (htop : topDelta = maximalConcentration (singletonConvexFamily B)) :
    topDelta ≤ 1 := by
  rw [htop]
  exact maximalConcentration_singletonConvexFamily_le_one B

#print axioms concentration_singletonConvexFamily_le_one
#print axioms maximalConcentration_singletonConvexFamily_le_one
#print axioms top_le_one_of_eq_singleton

end

end FamilyStickyTopScaleNormalizationV5

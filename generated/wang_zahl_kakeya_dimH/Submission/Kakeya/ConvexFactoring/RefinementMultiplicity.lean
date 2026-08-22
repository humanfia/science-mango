import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {F : ConvexFamily ι} {Y : Shading F}

/-- A quantitative refinement gives the direction-safe cross-multiplied
comparison of average multiplicities. This statement remains meaningful
when either shaded union has zero volume. -/
theorem IndexedShadingRefinement.averageMultiplicity_cross_le
    (R : IndexedShadingRefinement Y) (loss : ℕ)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass) :
    Y.shadingMass * volume R.shading.shadedUnion ≤
      (loss • R.shading.shadingMass) * volume Y.shadedUnion := by
  calc
    Y.shadingMass * volume R.shading.shadedUnion ≤
        (loss • R.shading.shadingMass) * volume R.shading.shadedUnion :=
      mul_le_mul' hretained le_rfl
    _ ≤ (loss • R.shading.shadingMass) * volume Y.shadedUnion := by
      exact mul_le_mul' le_rfl (measure_mono R.shadedUnion_subset)

/-- The quotient form of the refinement multiplicity inequality. The
direction is `original ≤ loss · refined`: shrinking the shaded union can
increase average multiplicity, not decrease it. `ENNReal` monotonicity makes
the statement valid without nonzero-volume side conditions. -/
theorem IndexedShadingRefinement.averageMultiplicity_le
    (R : IndexedShadingRefinement Y) (loss : ℕ)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass) :
    Y.averageMultiplicity ≤ loss • R.shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  calc
    Y.shadingMass / volume Y.shadedUnion ≤
        (loss • R.shading.shadingMass) / volume Y.shadedUnion :=
      ENNReal.div_le_div_right hretained _
    _ ≤ (loss • R.shading.shadingMass) / volume R.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono R.shadedUnion_subset) _
    _ = loss • (R.shading.shadingMass / volume R.shading.shadedUnion) := by
      simp only [nsmul_eq_mul, div_eq_mul_inv]
      ac_rfl

end

end Submission.Kakeya.ConvexFactoring

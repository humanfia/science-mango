import ChallengeDeps

open scoped MeasureTheory ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya

open LeanEval.Analysis.WangZahlKakeya

/-- Every subset of three-dimensional Euclidean space has Hausdorff dimension
at most the ambient dimension. -/
theorem dimH_le_three (K : Set Space) : dimH K ≤ 3 := by
  calc
    dimH K ≤ dimH (Set.univ : Set Space) := dimH_mono (Set.subset_univ K)
    _ = 3 := by simpa using Real.dimH_univ_eq_finrank Space

/-- A specialized bridge from infinite Hausdorff measure to a lower bound on
the Hausdorff dimension of a subset of three-dimensional Euclidean space. -/
theorem le_dimH_of_hausdorffMeasure_eq_top_space {K : Set Space} {d : ℝ≥0}
    (h : μH[d] K = ∞) : (d : ℝ≥0∞) ≤ dimH K :=
  le_dimH_of_hausdorffMeasure_eq_top h

end Submission.Kakeya

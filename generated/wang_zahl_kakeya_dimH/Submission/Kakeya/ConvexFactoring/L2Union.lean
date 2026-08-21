import Submission.Kakeya.ConvexGeometry.Shading

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-- Cauchy--Schwarz for a nonnegative function supported on a measurable set,
in a division-free `ENNReal` form. -/
theorem lintegral_sq_le_measure_mul_lintegral_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hfs : ∀ x, x ∉ s → f x = 0) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ μ s * ∫⁻ x, (f x) ^ 2 ∂μ := by
  let oneOn : α → ℝ≥0∞ := s.indicator fun _ ↦ 1
  have honeOn : Measurable oneOn := measurable_const.indicator hs
  have hmul : (fun x ↦ f x * oneOn x) = f := by
    funext x
    by_cases hx : x ∈ s
    · simp [oneOn, Set.indicator_of_mem hx]
    · simp [oneOn, hx, hfs x hx]
  have hone_sq : (fun x ↦ oneOn x ^ (2 : ℝ)) = oneOn := by
    funext x
    by_cases hx : x ∈ s
    · simp [oneOn, Set.indicator_of_mem hx]
    · simp [oneOn, hx]
  have hone_int : (∫⁻ x, oneOn x ∂μ) = μ s := by
    dsimp [oneOn]
    exact lintegral_indicator_one hs
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr (by norm_num)) hf honeOn.aemeasurable
  change (∫⁻ x, f x * oneOn x ∂μ) ≤ _ at hholder
  rw [hmul, hone_sq, hone_int] at hholder
  simp only [ENNReal.rpow_two] at hholder
  have hsquared := pow_le_pow_left₀
    (show (0 : ℝ≥0∞) ≤ (∫⁻ x, f x ∂μ) from bot_le) hholder 2
  calc
    (∫⁻ x, f x ∂μ) ^ 2
        ≤ (((∫⁻ x, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ))) *
            (μ s) ^ (1 / (2 : ℝ))) ^ 2 := hsquared
    _ = (∫⁻ x, f x ^ 2 ∂μ) * μ s := by
      rw [mul_pow]
      simp only [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
    _ = μ s * ∫⁻ x, f x ^ 2 ∂μ := mul_comm _ _

variable {ι : Type*} {F : ConvexFamily ι} (Y : Shading F)

/-- The `ENNReal`-valued point multiplicity is measurable. -/
theorem measurable_pointMultiplicity [Fintype ι] :
    Measurable fun x ↦ (Y.pointMultiplicity x : ℝ≥0∞) := by
  classical
  simp_rw [Y.pointMultiplicity_cast_eq_sum_indicator]
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator (Y.measurable_carrier i)

/-- The second multiplicity moment is the sum of all pairwise shaded overlaps. -/
theorem lintegral_pointMultiplicity_sq [Fintype ι] :
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) =
      ∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j) := by
  classical
  have hexpand (x : Space) :
      (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 =
        ∑ i, ∑ j,
          (Y.carrier i ∩ Y.carrier j).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    rw [Y.pointMultiplicity_cast_eq_sum_indicator, pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrFun (Set.inter_indicator_one (M₀ := ℝ≥0∞)
      (s := Y.carrier i) (t := Y.carrier j)).symm x
  simp_rw [hexpand]
  calc
    (∫⁻ x, ∑ i, ∑ j,
        (Y.carrier i ∩ Y.carrier j).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂volume)
        = ∑ i, ∫⁻ x, ∑ j,
            (Y.carrier i ∩ Y.carrier j).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂volume := by
          apply lintegral_finsetSum
          intro i hi
          apply Finset.measurable_fun_sum
          intro j hj
          exact measurable_const.indicator
            ((Y.measurable_carrier i).inter (Y.measurable_carrier j))
    _ = ∑ i, ∑ j, ∫⁻ x,
          (Y.carrier i ∩ Y.carrier j).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂volume := by
          apply Finset.sum_congr rfl
          intro i hi
          apply lintegral_finsetSum
          intro j hj
          exact measurable_const.indicator ((Y.measurable_carrier i).inter (Y.measurable_carrier j))
    _ = ∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact lintegral_indicator_one ((Y.measurable_carrier i).inter (Y.measurable_carrier j))

/-- The Córdoba `L²` lower bound for the union of a finite shaded family. -/
theorem shadingMass_sq_le_volume_shadedUnion_mul_secondMoment [Fintype ι] :
    Y.shadingMass ^ 2 ≤ volume Y.shadedUnion *
      ∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume := by
  rw [← Y.lintegral_pointMultiplicity]
  apply lintegral_sq_le_measure_mul_lintegral_sq volume Y.shadedUnion_measurableSet
  · exact (measurable_pointMultiplicity Y).aemeasurable
  · intro x hx
    have hnotpos : ¬ 0 < Y.pointMultiplicity x := by
      simpa [Y.pointMultiplicity_pos_iff_mem_shadedUnion x] using hx
    have hzero : Y.pointMultiplicity x = 0 := Nat.eq_zero_of_not_pos hnotpos
    simp [hzero]

/-- The same lower bound with the second moment expanded as pairwise overlaps. -/
theorem shadingMass_sq_le_volume_shadedUnion_mul_overlapSum [Fintype ι] :
    Y.shadingMass ^ 2 ≤ volume Y.shadedUnion *
      ∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j) := by
  rw [← lintegral_pointMultiplicity_sq Y]
  exact shadingMass_sq_le_volume_shadedUnion_mul_secondMoment Y

end Submission.Kakeya.ConvexFactoring

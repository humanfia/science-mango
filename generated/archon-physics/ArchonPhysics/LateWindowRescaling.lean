import ArchonPhysics.EquipartitionEntropy

/-!
# Rescaling late-time equipartition windows

This module transfers the late-window observables under the kinetic time
change `tau = g² * t`.  The Jacobian is supplied by Mathlib's
`intervalIntegral.integral_comp_mul_left`; it is not hidden in a definitional
reduction.  The API also records interval integrability explicitly, even
though Mathlib's change-of-variables identity itself is valid for its totalized
integral without that assumption.
-/

namespace ArchonPhysics.LateWindowRescaling

open MeasureTheory
open ArchonPhysics.EquipartitionEntropy

noncomputable section

/--
Interval integrability transfers from the kinetic window to the physical-time
window under `tau = g² * t`.
-/
theorem intervalIntegrable_timeRescaled
    {mode : Type} (Eg Eone : Real → mode → Real)
    (mu T g : Real) (i : mode) (hg : g ≠ 0)
    (hrescale : ∀ t k, Eg t k = Eone (g ^ 2 * t) k)
    (hEone : IntervalIntegrable (fun tau => Eone tau i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T)) :
    IntervalIntegrable (fun t => Eg t i) volume (mu * T) T := by
  have hg_sq_ne : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hEone' : IntervalIntegrable (fun tau => Eone tau i) volume
      (g ^ 2 * (mu * T)) (g ^ 2 * T) := by
    convert hEone using 1
    ring
  have hcomp := hEone'.comp_mul_left (c := g ^ 2)
  have hcomp' : IntervalIntegrable (fun t => Eone (g ^ 2 * t) i)
      volume (mu * T) T := by
    simpa [hg_sq_ne] using hcomp
  exact hcomp'.congr (fun t _ => (hrescale t i).symm)

/--
The late-window average is invariant under kinetic time rescaling.  Positivity
of the window length is explicit, and the proof uses the `g²` Jacobian from
Mathlib's interval-integral substitution theorem.
-/
theorem lateWindowAverage_rescaling
    {mode : Type} (Eg Eone : Real → mode → Real)
    (mu T g : Real) (hg : g ≠ 0) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : ∀ t i, Eg t i = Eone (g ^ 2 * t) i)
    (hEone : ∀ i, IntervalIntegrable (fun tau => Eone tau i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T)) :
    lateWindowAverage Eg mu T =
      lateWindowAverage Eone mu (g ^ 2 * T) := by
  have hg_sq_ne : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hg_sq_pos : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hwindow_pos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmu_lt_one) hT
  have hscaledT : 0 < g ^ 2 * T := mul_pos hg_sq_pos hT
  have hscaled_window_pos : 0 < (1 - mu) * (g ^ 2 * T) :=
    mul_pos (sub_pos.mpr hmu_lt_one) hscaledT
  have _hEg : ∀ i, IntervalIntegrable (fun t => Eg t i) volume (mu * T) T :=
    fun i => intervalIntegrable_timeRescaled Eg Eone mu T g i hg hrescale (hEone i)
  funext i
  unfold lateWindowAverage
  have hintegral :
      (∫ t in mu * T..T, Eg t i) =
        ∫ t in mu * T..T, Eone (g ^ 2 * t) i :=
    intervalIntegral.integral_congr (fun t _ => hrescale t i)
  rw [hintegral]
  rw [intervalIntegral.integral_comp_mul_left
    (f := fun tau => Eone tau i) hg_sq_ne]
  simp only [smul_eq_mul]
  rw [show g ^ 2 * (mu * T) = mu * (g ^ 2 * T) by ring]
  have hnormalizer :
      ((1 - mu) * T)⁻¹ * (g ^ 2)⁻¹ =
        ((1 - mu) * (g ^ 2 * T))⁻¹ := by
    field_simp [ne_of_gt hwindow_pos, hg_sq_ne,
      ne_of_gt hscaled_window_pos]
  calc
    ((1 - mu) * T)⁻¹ *
        ((g ^ 2)⁻¹ * ∫ tau in mu * (g ^ 2 * T)..g ^ 2 * T, Eone tau i) =
      (((1 - mu) * T)⁻¹ * (g ^ 2)⁻¹) *
        ∫ tau in mu * (g ^ 2 * T)..g ^ 2 * T, Eone tau i := by ring
    _ = ((1 - mu) * (g ^ 2 * T))⁻¹ *
        ∫ tau in mu * (g ^ 2 * T)..g ^ 2 * T, Eone tau i := by
      rw [hnormalizer]

/-- Global continuity is a convenient sufficient hypothesis for the rescaling theorem. -/
theorem lateWindowAverage_rescaling_of_continuous
    {mode : Type} (Eg Eone : Real → mode → Real)
    (mu T g : Real) (hg : g ≠ 0) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : ∀ t i, Eg t i = Eone (g ^ 2 * t) i)
    (hEone : ∀ i, Continuous (fun tau => Eone tau i)) :
    lateWindowAverage Eg mu T =
      lateWindowAverage Eone mu (g ^ 2 * T) := by
  exact lateWindowAverage_rescaling Eg Eone mu T g hg hmu_lt_one hT
    hrescale (fun i => (hEone i).intervalIntegrable _ _)

/-- Normalized late-window modal weights are unchanged by kinetic time rescaling. -/
theorem normalizedWeights_lateWindowAverage_rescaling
    {mode : Type} [Fintype mode]
    (Eg Eone : Real → mode → Real)
    (mu T g : Real) (hg : g ≠ 0) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : ∀ t i, Eg t i = Eone (g ^ 2 * t) i)
    (hEone : ∀ i, IntervalIntegrable (fun tau => Eone tau i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T)) :
    normalizedWeights (lateWindowAverage Eg mu T) =
      normalizedWeights (lateWindowAverage Eone mu (g ^ 2 * T)) := by
  rw [lateWindowAverage_rescaling Eg Eone mu T g hg hmu_lt_one hT
    hrescale hEone]

/-- The finite `l1` equipartition distance is unchanged by kinetic time rescaling. -/
theorem l1Distance_lateWindowAverage_rescaling
    {mode : Type} [Fintype mode]
    (Eg Eone : Real → mode → Real)
    (mu T g : Real) (hg : g ≠ 0) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : ∀ t i, Eg t i = Eone (g ^ 2 * t) i)
    (hEone : ∀ i, IntervalIntegrable (fun tau => Eone tau i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T)) :
    l1Distance (normalizedWeights (lateWindowAverage Eg mu T))
        (uniformWeights : mode → Real) =
      l1Distance (normalizedWeights
        (lateWindowAverage Eone mu (g ^ 2 * T)))
        (uniformWeights : mode → Real) := by
  rw [normalizedWeights_lateWindowAverage_rescaling Eg Eone mu T g hg
    hmu_lt_one hT hrescale hEone]

/-- Approximate equipartition is equivalent on the two corresponding positive windows. -/
theorem approxEquipartition_rescaling_iff
    {mode : Type} [Fintype mode] [Nonempty mode]
    (Eg Eone : Real → mode → Real)
    (mu delta T g : Real) (hg : g ≠ 0)
    (hmu_nonneg : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : ∀ t i, Eg t i = Eone (g ^ 2 * t) i)
    (hEone : ∀ i, IntervalIntegrable (fun tau => Eone tau i) volume
      (mu * (g ^ 2 * T)) (g ^ 2 * T)) :
    ApproxEquipartition Eg mu delta T ↔
      ApproxEquipartition Eone mu delta (g ^ 2 * T) := by
  have havg := lateWindowAverage_rescaling Eg Eone mu T g hg
    hmu_lt_one hT hrescale hEone
  have hscaledT : 0 < g ^ 2 * T :=
    mul_pos (sq_pos_of_ne_zero hg) hT
  unfold ApproxEquipartition
  rw [havg]
  simp only [hmu_nonneg, hmu_lt_one, hT, hscaledT, true_and]

end

end ArchonPhysics.LateWindowRescaling

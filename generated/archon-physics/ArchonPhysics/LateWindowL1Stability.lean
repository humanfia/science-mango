import ArchonPhysics.NormalizedL1Stability

/-!
# `l1` stability of late-window modal-energy averages

Late-window averaging is Lipschitz from time-integrated modal `l1` error to
the finite modal `l1` error.  Combining this with normalization stability
reduces the final microscopic observable estimate to an unnormalized energy
estimate plus a positive total-energy floor.

No microscopic-to-kinetic convergence is asserted in this module.
-/

namespace ArchonPhysics.LateWindowL1Stability

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.NormalizedL1Stability

noncomputable section

/-- Time-integrated finite modal `l1` error on the late window. -/
def windowIntegratedL1Error {ι : Type} [Fintype ι]
    (E K : Real → ι → Real) (mu T : Real) : Real :=
  ∑ i, ∫ t in mu * T..T, |E t i - K t i|

/-- Late-window averaging converts integrated modal `l1` error into raw
late-window `l1` error with the exact reciprocal-window factor. -/
theorem l1Distance_lateWindowAverage_le
    {ι : Type} [Fintype ι]
    (E K : Real → ι → Real) (mu T : Real)
    (_hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T) :
    l1Distance (lateWindowAverage E mu T)
        (lateWindowAverage K mu T) ≤
      ((1 - mu) * T)⁻¹ * windowIntegratedL1Error E K mu T := by
  have hwindow_pos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmu_lt_one) hT
  have hfactor_nonneg : 0 ≤ ((1 - mu) * T)⁻¹ :=
    inv_nonneg.mpr hwindow_pos.le
  have hinterval : mu * T ≤ T := by
    calc
      mu * T ≤ 1 * T :=
        mul_le_mul_of_nonneg_right hmu_lt_one.le hT.le
      _ = T := one_mul T
  unfold l1Distance windowIntegratedL1Error lateWindowAverage
  calc
    (∑ i, |((1 - mu) * T)⁻¹ * (∫ t in mu * T..T, E t i) -
        ((1 - mu) * T)⁻¹ * (∫ t in mu * T..T, K t i)|) ≤
        ∑ i, ((1 - mu) * T)⁻¹ *
          ∫ t in mu * T..T, |E t i - K t i| := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        |((1 - mu) * T)⁻¹ * (∫ t in mu * T..T, E t i) -
            ((1 - mu) * T)⁻¹ * (∫ t in mu * T..T, K t i)| =
            ((1 - mu) * T)⁻¹ *
              |(∫ t in mu * T..T, E t i) -
                ∫ t in mu * T..T, K t i| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hfactor_nonneg]
        _ = ((1 - mu) * T)⁻¹ *
              |∫ t in mu * T..T, (E t i - K t i)| := by
          rw [intervalIntegral.integral_sub (hE i) (hK i)]
        _ ≤ ((1 - mu) * T)⁻¹ *
              ∫ t in mu * T..T, |E t i - K t i| := by
          gcongr
          exact intervalIntegral.abs_integral_le_integral_abs hinterval
    _ = ((1 - mu) * T)⁻¹ *
        ∑ i, ∫ t in mu * T..T, |E t i - K t i| := by
      rw [Finset.mul_sum]

/-- If the integrated error is at most window length times `epsilon`, then
the raw late-window profiles are within `epsilon` in `l1`. -/
theorem l1Distance_lateWindowAverage_le_epsilon
    {ι : Type} [Fintype ι]
    (E K : Real → ι → Real) (mu T epsilon : Real)
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (_hepsilon : 0 ≤ epsilon)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T)
    (herror : windowIntegratedL1Error E K mu T ≤
      ((1 - mu) * T) * epsilon) :
    l1Distance (lateWindowAverage E mu T)
      (lateWindowAverage K mu T) ≤ epsilon := by
  have hwindow_pos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmu_lt_one) hT
  calc
    l1Distance (lateWindowAverage E mu T)
        (lateWindowAverage K mu T) ≤
        ((1 - mu) * T)⁻¹ * windowIntegratedL1Error E K mu T :=
      l1Distance_lateWindowAverage_le E K mu T hmu hmu_lt_one hT hE hK
    _ ≤ ((1 - mu) * T)⁻¹ * (((1 - mu) * T) * epsilon) := by
      gcongr
    _ = epsilon := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hwindow_pos), one_mul]

/-- Combined late-window and normalization estimate.  The final observable
is controlled by the raw time-integrated error and a positive energy floor. -/
theorem normalized_l1Distance_lateWindowAverage_le
    {ι : Type} [Fintype ι]
    (E K : Real → ι → Real) (mu T : Real) {energyFloor : Real}
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hfloor : 0 < energyFloor)
    (hEFloor : energyFloor ≤ totalWeight (lateWindowAverage E mu T))
    (hKTotal : 0 < totalWeight (lateWindowAverage K mu T))
    (hKNonneg : ∀ i, 0 ≤ lateWindowAverage K mu T i)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T) :
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (normalizedWeights (lateWindowAverage K mu T)) ≤
      (2 / energyFloor) * (((1 - mu) * T)⁻¹ *
        windowIntegratedL1Error E K mu T) := by
  have hconstant_nonneg : 0 ≤ 2 / energyFloor := by positivity
  calc
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (normalizedWeights (lateWindowAverage K mu T)) ≤
        (2 / energyFloor) *
          l1Distance (lateWindowAverage E mu T)
            (lateWindowAverage K mu T) :=
      l1Distance_normalizedWeights_le_of_lowerBound
        (lateWindowAverage E mu T) (lateWindowAverage K mu T)
        hfloor hEFloor hKTotal hKNonneg
    _ ≤ (2 / energyFloor) * (((1 - mu) * T)⁻¹ *
        windowIntegratedL1Error E K mu T) :=
      mul_le_mul_of_nonneg_left
        (l1Distance_lateWindowAverage_le E K mu T
          hmu hmu_lt_one hT hE hK) hconstant_nonneg

end

end ArchonPhysics.LateWindowL1Stability

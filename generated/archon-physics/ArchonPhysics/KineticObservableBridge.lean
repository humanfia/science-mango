import ArchonPhysics.LateWindowL1Stability

/-!
# Microscopic-to-kinetic-to-equipartition observable bridge

This module composes two explicit approximation premises:

1. a microscopic modal-energy profile is close, in time-integrated raw
   finite `l1`, to a kinetic profile on the late window;
2. the normalized late-window kinetic profile is close to uniform.

A positive microscopic energy floor makes normalization stable.  The result
is the normalized late-window `l1` estimate used by the thermalization
observable.  No microscopic limit, kinetic relaxation, or collision theorem
is asserted here; all such analytic input remains a hypothesis.
-/

namespace ArchonPhysics.KineticObservableBridge

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.LateWindowL1Stability

noncomputable section

/-- The finite modal `l1` distance satisfies the triangle inequality. -/
theorem l1Distance_triangle {ι : Type} [Fintype ι]
    (w v u : ι → Real) :
    l1Distance w u ≤ l1Distance w v + l1Distance v u := by
  unfold l1Distance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hdecomp : w i - u i = (w i - v i) + (v i - u i) := by ring
  rw [hdecomp]
  exact abs_add_le _ _

/-- Exact error bookkeeping for the observable bridge.

The first term is the normalized microscopic-to-kinetic late-window error;
the second is the supplied normalized kinetic relaxation error. -/
theorem normalized_lateWindow_l1_le_micro_add_kinetic
    {ι : Type} [Fintype ι] [Nonempty ι]
    (E K : Real → ι → Real) (mu T kineticError : Real)
    {energyFloor : Real}
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hfloor : 0 < energyFloor)
    (hEFloor : energyFloor ≤ totalWeight (lateWindowAverage E mu T))
    (hKTotal : 0 < totalWeight (lateWindowAverage K mu T))
    (hKNonneg : ∀ i, 0 ≤ lateWindowAverage K mu T i)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T)
    (hKineticRelaxation :
      l1Distance (normalizedWeights (lateWindowAverage K mu T))
        (uniformWeights : ι → Real) ≤ kineticError) :
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (uniformWeights : ι → Real) ≤
      (2 / energyFloor) * (((1 - mu) * T)⁻¹ *
        windowIntegratedL1Error E K mu T) + kineticError := by
  calc
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (uniformWeights : ι → Real) ≤
        l1Distance (normalizedWeights (lateWindowAverage E mu T))
          (normalizedWeights (lateWindowAverage K mu T)) +
        l1Distance (normalizedWeights (lateWindowAverage K mu T))
          (uniformWeights : ι → Real) :=
      l1Distance_triangle _ _ _
    _ ≤ (2 / energyFloor) * (((1 - mu) * T)⁻¹ *
          windowIntegratedL1Error E K mu T) + kineticError := by
      gcongr
      · exact normalized_l1Distance_lateWindowAverage_le E K mu T
          hmu hmu_lt_one hT hfloor hEFloor hKTotal hKNonneg hE hK

/-- If the integrated microscopic error is at most the window length times
`microError`, the final normalized error is at most
`(2 / energyFloor) * microError + kineticError`. -/
theorem normalized_lateWindow_l1_le_of_error_budgets
    {ι : Type} [Fintype ι] [Nonempty ι]
    (E K : Real → ι → Real)
    (mu T microError kineticError : Real) {energyFloor : Real}
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hfloor : 0 < energyFloor)
    (hEFloor : energyFloor ≤ totalWeight (lateWindowAverage E mu T))
    (hKTotal : 0 < totalWeight (lateWindowAverage K mu T))
    (hKNonneg : ∀ i, 0 ≤ lateWindowAverage K mu T i)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T)
    (hMicroscopicApproximation : windowIntegratedL1Error E K mu T ≤
      ((1 - mu) * T) * microError)
    (hKineticRelaxation :
      l1Distance (normalizedWeights (lateWindowAverage K mu T))
        (uniformWeights : ι → Real) ≤ kineticError) :
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (uniformWeights : ι → Real) ≤
      (2 / energyFloor) * microError + kineticError := by
  have hwindow_pos : 0 < (1 - mu) * T :=
    mul_pos (sub_pos.mpr hmu_lt_one) hT
  have hscaled : ((1 - mu) * T)⁻¹ *
      windowIntegratedL1Error E K mu T ≤ microError := by
    calc
      ((1 - mu) * T)⁻¹ * windowIntegratedL1Error E K mu T ≤
          ((1 - mu) * T)⁻¹ * (((1 - mu) * T) * microError) := by
        gcongr
      _ = microError := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hwindow_pos), one_mul]
  have hbridge := normalized_lateWindow_l1_le_micro_add_kinetic
    E K mu T kineticError hmu hmu_lt_one hT hfloor hEFloor
    hKTotal hKNonneg hE hK hKineticRelaxation
  calc
    l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (uniformWeights : ι → Real) ≤
        (2 / energyFloor) * (((1 - mu) * T)⁻¹ *
          windowIntegratedL1Error E K mu T) + kineticError := hbridge
    _ ≤ (2 / energyFloor) * microError + kineticError := by
      have hcoefficient : 0 ≤ 2 / energyFloor := by positivity
      gcongr

/-- The same composition discharged directly into the repository's
`ApproxEquipartition` observable. -/
theorem approxEquipartition_of_microscopic_kinetic_bridge
    {ι : Type} [Fintype ι] [Nonempty ι]
    (E K : Real → ι → Real)
    (mu T delta microError kineticError : Real) {energyFloor : Real}
    (hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hfloor : 0 < energyFloor)
    (hEFloor : energyFloor ≤ totalWeight (lateWindowAverage E mu T))
    (hKTotal : 0 < totalWeight (lateWindowAverage K mu T))
    (hKNonneg : ∀ i, 0 ≤ lateWindowAverage K mu T i)
    (hE : ∀ i, IntervalIntegrable (fun t ↦ E t i)
      MeasureTheory.volume (mu * T) T)
    (hK : ∀ i, IntervalIntegrable (fun t ↦ K t i)
      MeasureTheory.volume (mu * T) T)
    (hMicroscopicApproximation : windowIntegratedL1Error E K mu T ≤
      ((1 - mu) * T) * microError)
    (hKineticRelaxation :
      l1Distance (normalizedWeights (lateWindowAverage K mu T))
        (uniformWeights : ι → Real) ≤ kineticError)
    (hErrorBudget : (2 / energyFloor) * microError + kineticError ≤ delta) :
    ApproxEquipartition E mu delta T := by
  refine ⟨hmu, hmu_lt_one, hT, hfloor.trans_le hEFloor, ?_⟩
  exact (normalized_lateWindow_l1_le_of_error_budgets E K mu T
    microError kineticError hmu hmu_lt_one hT hfloor hEFloor
    hKTotal hKNonneg hE hK hMicroscopicApproximation
    hKineticRelaxation).trans hErrorBudget

end

end ArchonPhysics.KineticObservableBridge

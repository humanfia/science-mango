import ArchonPhysics.PeriodicFourierGridTensorQuadrature

/-!
# Lipschitz tensor quadrature on the periodic Fourier grid

For finite-time resonance integrands, second derivatives can be unnecessarily
expensive while coordinatewise Lipschitz constants remain quantitative.  This
module proves the corresponding two-dimensional deterministic quadrature
estimate.  If the two coordinate constants are `L₁` and `L₂`, then

`|grid quadrature - iterated integral| ≤ (2π)³ (L₁ + L₂) / N`.

The continuity of the second-coordinate marginal is not assumed.  It is
derived here from fibrewise continuity and the uniform first-coordinate
Lipschitz estimate.  The last theorem specializes the joint limit to constants
of size `Cᵢ T²`, making the required window `T² / N → 0` explicit.  These are
quadrature statements only; no kinetic equation or dynamical limit is used.
-/

namespace ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open ArchonPhysics.PeriodicFourierGridQuadrature
open ArchonPhysics.PeriodicFourierGridTensorQuadrature
open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

/-! ## The integrated marginal inherits the first-coordinate modulus -/

/-- Integrating a fibre of length `2π` multiplies a uniform
first-coordinate Lipschitz constant by `2π`.  Fibrewise continuity supplies
the interval integrability needed to subtract the two integrals. -/
theorem abs_secondCoordinateIntervalMarginal_sub_le
    (F : Real → Real → Real) {L₁ : Real}
    (hcontinuous₂ : ∀ x, ContinuousOn (fun y ↦ F x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₁ : ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x' y| ≤ L₁ * |x - x'|)
    {x x' : Real} (hx : x ∈ Icc (0 : Real) (2 * Real.pi))
    (hx' : x' ∈ Icc (0 : Real) (2 * Real.pi)) :
    |secondCoordinateIntervalMarginal F x -
        secondCoordinateIntervalMarginal F x'| ≤
      (2 * Real.pi * L₁) * |x - x'| := by
  have hintx : IntervalIntegrable (fun y ↦ F x y) volume
      (0 : Real) (2 * Real.pi) :=
    (hcontinuous₂ x).intervalIntegrable_of_Icc (by positivity)
  have hintx' : IntervalIntegrable (fun y ↦ F x' y) volume
      (0 : Real) (2 * Real.pi) :=
    (hcontinuous₂ x').intervalIntegrable_of_Icc (by positivity)
  rw [secondCoordinateIntervalMarginal,
    secondCoordinateIntervalMarginal,
    ← intervalIntegral.integral_sub hintx hintx', ← Real.norm_eq_abs]
  calc
    ‖∫ y in (0 : Real)..(2 * Real.pi), F x y - F x' y‖ ≤
        (L₁ * |x - x'|) * |2 * Real.pi - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hyIcc : y ∈ Icc (0 : Real) (2 * Real.pi) := by
        rw [uIoc_of_le (by positivity : (0 : Real) ≤ 2 * Real.pi)] at hy
        exact ⟨hy.1.le, hy.2⟩
      simpa only [Real.norm_eq_abs] using
        hlipschitz₁ y hyIcc x hx x' hx'
    _ = (2 * Real.pi * L₁) * |x - x'| := by
      rw [sub_zero, abs_of_pos (by positivity : (0 : Real) < 2 * Real.pi)]
      ring

/-- The marginal is Lipschitz on the Brillouin interval with the derived
constant `2π L₁`. -/
theorem secondCoordinateIntervalMarginal_lipschitzOnWith
    (F : Real → Real → Real) {L₁ : Real} (hL₁ : 0 ≤ L₁)
    (hcontinuous₂ : ∀ x, ContinuousOn (fun y ↦ F x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₁ : ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x' y| ≤ L₁ * |x - x'|) :
    LipschitzOnWith
      (⟨2 * Real.pi * L₁, mul_nonneg (by positivity) hL₁⟩ : NNReal)
      (secondCoordinateIntervalMarginal F)
      (Icc (0 : Real) (2 * Real.pi)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx x' hx'
  change |secondCoordinateIntervalMarginal F x -
    secondCoordinateIntervalMarginal F x'| ≤
      (2 * Real.pi * L₁) * |x - x'|
  exact
    abs_secondCoordinateIntervalMarginal_sub_le
      F hcontinuous₂ hlipschitz₁ hx hx'

/-- In particular, marginal continuity follows from the stated coordinate
hypotheses; it is not an independent analytic input. -/
theorem secondCoordinateIntervalMarginal_continuousOn
    (F : Real → Real → Real) {L₁ : Real} (hL₁ : 0 ≤ L₁)
    (hcontinuous₂ : ∀ x, ContinuousOn (fun y ↦ F x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₁ : ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x' y| ≤ L₁ * |x - x'|) :
    ContinuousOn (secondCoordinateIntervalMarginal F)
      (Icc (0 : Real) (2 * Real.pi)) :=
  (secondCoordinateIntervalMarginal_lipschitzOnWith
    F hL₁ hcontinuous₂ hlipschitz₁).continuousOn

/-! ## Two-dimensional estimate -/

/-- Coordinatewise periodicity, fibre continuity, and uniform coordinate
Lipschitz bounds imply an explicit `O((L₁+L₂)/N)` tensor quadrature
estimate.  First-coordinate continuity is already contained in
`hlipschitz₁`; the marginal continuity used by the outer quadrature is
proved above. -/
theorem abs_periodicFourierTensorGridQuadrature_sub_integral_le_of_lipschitz
    (N : Nat) [NeZero N] (F : Real → Real → Real)
    {L₁ L₂ : Real} (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hendpoint₂ : ∀ x, F x 0 = F x (2 * Real.pi))
    (hcontinuous₂ : ∀ x, ContinuousOn (fun y ↦ F x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x y'| ≤ L₂ * |y - y'|)
    (hendpoint₁ : ∀ y, F 0 y = F (2 * Real.pi) y)
    (hlipschitz₁ : ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F x y - F x' y| ≤ L₁ * |x - x'|) :
    |periodicFourierTensorGridQuadrature N F -
      periodicFourierTensorIntervalIntegral F| ≤
      (2 * Real.pi) ^ 3 * (L₁ + L₂) / (N : Real) := by
  let length : Real := 2 * Real.pi
  let step : Real := length / (N : Real)
  let marginal : Real → Real := secondCoordinateIntervalMarginal F
  let fibreGrid : Real → Real := fun x ↦
    step * ∑ k₂ : Site N, F x (gridWaveNumber N k₂)
  let error₂ : Real := L₂ * length ^ 2 / (N : Real)
  let error₁ : Real := (length * L₁) * length ^ 2 / (N : Real)
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hstepPos : 0 < step := by
    dsimp [step, length]
    positivity
  have herror₂ : 0 ≤ error₂ := by
    dsimp [error₂, length]
    positivity
  have hfibreError (x : Real) :
      |fibreGrid x - marginal x| ≤ error₂ := by
    simpa [fibreGrid, marginal, step, error₂, length,
      secondCoordinateIntervalMarginal] using
      (abs_fourierGrid_sum_sub_integral_le_of_lipschitz
        N (fun y ↦ F x y) hL₂ (hendpoint₂ x)
          (hcontinuous₂ x) (hlipschitz₂ x))
  have hmarginalEndpoint : marginal 0 = marginal length := by
    dsimp [marginal, secondCoordinateIntervalMarginal, length]
    apply intervalIntegral.integral_congr
    intro y _hy
    exact hendpoint₁ y
  have hmarginalContinuous :
      ContinuousOn marginal (Icc (0 : Real) length) := by
    simpa [marginal, length] using
      secondCoordinateIntervalMarginal_continuousOn
        F hL₁ hcontinuous₂ hlipschitz₁
  have hmarginalLipschitz :
      ∀ x ∈ Icc (0 : Real) length,
      ∀ x' ∈ Icc (0 : Real) length,
        |marginal x - marginal x'| ≤
          (length * L₁) * |x - x'| := by
    intro x hx x' hx'
    simpa [marginal, length] using
      abs_secondCoordinateIntervalMarginal_sub_le
        F hcontinuous₂ hlipschitz₁ hx hx'
  have hmarginalError :
      |step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
        ∫ x in (0 : Real)..length, marginal x| ≤ error₁ := by
    simpa [step, length, marginal, error₁] using
      (abs_fourierGrid_sum_sub_integral_le_of_lipschitz
        N marginal (mul_nonneg (by positivity) hL₁)
          hmarginalEndpoint hmarginalContinuous hmarginalLipschitz)
  have hfibreTotal :
      |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
        step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)| ≤
          length * error₂ := by
    calc
      |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
          step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)| =
          |step * ∑ k₁ : Site N,
            (fibreGrid (gridWaveNumber N k₁) -
              marginal (gridWaveNumber N k₁))| := by
            congr 1
            rw [Finset.sum_sub_distrib, mul_sub]
      _ = |step| * |∑ k₁ : Site N,
          (fibreGrid (gridWaveNumber N k₁) -
            marginal (gridWaveNumber N k₁))| := abs_mul _ _
      _ ≤ |step| * ∑ k₁ : Site N,
          |fibreGrid (gridWaveNumber N k₁) -
            marginal (gridWaveNumber N k₁)| :=
        mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg step)
      _ ≤ |step| * ∑ _k₁ : Site N, error₂ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k₁ _hk₁ ↦
            hfibreError (gridWaveNumber N k₁))
          (abs_nonneg step)
      _ = length * error₂ := by
        rw [abs_of_pos hstepPos]
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
          nsmul_eq_mul]
        dsimp [step]
        field_simp [ne_of_gt hNpos]
  have hcombined :
      |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
        ∫ x in (0 : Real)..length, marginal x| ≤
          length * error₂ + error₁ := by
    calc
      |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
          ∫ x in (0 : Real)..length, marginal x| ≤
          |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
            step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)| +
          |step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
            ∫ x in (0 : Real)..length, marginal x| := by
        calc
          |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
              ∫ x in (0 : Real)..length, marginal x| =
              |(step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
                step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)) +
               (step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
                ∫ x in (0 : Real)..length, marginal x)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      _ ≤ length * error₂ + error₁ :=
        add_le_add hfibreTotal hmarginalError
  change
    |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
      ∫ x in (0 : Real)..length, marginal x| ≤
      (2 * Real.pi) ^ 3 * (L₁ + L₂) / (N : Real)
  exact hcombined.trans_eq (by
    dsimp [length, error₂, error₁]
    ring)

/-! ## Joint volume/time windows -/

/-- A sequence of coordinate Lipschitz constants satisfying
`(L₁(n)+L₂(n))/(n+1) → 0` gives convergence of tensor quadrature. -/
theorem periodicFourierTensorLipschitzQuadratureError_tendsto_zero
    (F : Nat → Real → Real → Real) (L₁ L₂ : Nat → Real)
    (hL₁ : ∀ n, 0 ≤ L₁ n) (hL₂ : ∀ n, 0 ≤ L₂ n)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hcontinuous₂ : ∀ n x, ContinuousOn (fun y ↦ F n x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ n x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x y'| ≤ L₂ n * |y - y'|)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hlipschitz₁ : ∀ n, ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x' y| ≤ L₁ n * |x - x'|)
    (hscale : Tendsto
      (fun n : Nat ↦ (L₁ n + L₂ n) / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        |periodicFourierTensorGridQuadrature (n + 1) (F n) -
          periodicFourierTensorIntervalIntegral (F n)|)
      atTop (nhds 0) := by
  let constant : Real := (2 * Real.pi) ^ 3
  have hupper : Tendsto
      (fun n : Nat ↦ constant *
        ((L₁ n + L₂ n) / (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hscale
  apply squeeze_zero' (g := fun n : Nat ↦ constant *
    ((L₁ n + L₂ n) / (((n + 1 : Nat) : Real))))
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      have hbound :=
        abs_periodicFourierTensorGridQuadrature_sub_integral_le_of_lipschitz
          (n + 1) (F n) (hL₁ n) (hL₂ n)
          (hendpoint₂ n) (hcontinuous₂ n) (hlipschitz₂ n)
          (hendpoint₁ n) (hlipschitz₁ n)
      exact hbound.trans_eq (by
        dsimp [constant]
        ring)
  · exact hupper

/-- If the coordinate constants are bounded by `C₁ T²` and `C₂ T²`,
the explicit sufficient joint volume/time window is `T²/(n+1) → 0`.
This is the deterministic interface needed for finite-time resonance
integrands with an `O(T²)` Lipschitz modulus. -/
theorem periodicFourierTensorQuadratureError_tendsto_zero_of_time_sq_div_volume
    (F : Nat → Real → Real → Real) (T : Nat → Real)
    {C₁ C₂ : Real} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hcontinuous₂ : ∀ n x, ContinuousOn (fun y ↦ F n x y)
      (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz₂ : ∀ n x,
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x y'| ≤
          (C₂ * (T n) ^ 2) * |y - y'|)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hlipschitz₁ : ∀ n, ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ x' ∈ Icc (0 : Real) (2 * Real.pi),
        |F n x y - F n x' y| ≤
          (C₁ * (T n) ^ 2) * |x - x'|)
    (htimeWindow : Tendsto
      (fun n : Nat ↦ (T n) ^ 2 / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        |periodicFourierTensorGridQuadrature (n + 1) (F n) -
          periodicFourierTensorIntervalIntegral (F n)|)
      atTop (nhds 0) := by
  apply periodicFourierTensorLipschitzQuadratureError_tendsto_zero
    F (fun n ↦ C₁ * (T n) ^ 2) (fun n ↦ C₂ * (T n) ^ 2)
      (fun n ↦ mul_nonneg hC₁ (sq_nonneg (T n)))
      (fun n ↦ mul_nonneg hC₂ (sq_nonneg (T n)))
      hendpoint₂ hcontinuous₂ hlipschitz₂
      hendpoint₁ hlipschitz₁
  have hscaled : Tendsto
      (fun n : Nat ↦ (C₁ + C₂) *
        ((T n) ^ 2 / (((n + 1 : Nat) : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul htimeWindow
  have heq :
      (fun n : Nat ↦
        (C₁ * (T n) ^ 2 + C₂ * (T n) ^ 2) /
          (((n + 1 : Nat) : Real))) =
      (fun n : Nat ↦ (C₁ + C₂) *
        ((T n) ^ 2 / (((n + 1 : Nat) : Real)))) := by
    funext n
    ring
  rw [heq]
  exact hscaled

end

end ArchonPhysics.PeriodicFourierGridTensorLipschitzQuadrature

import ArchonPhysics.PeriodicFourierGridQuadrature

/-!
# Tensor quadrature on the two-dimensional periodic Fourier grid

A fixed-output four-wave collision has two free Fourier momenta.  This module
applies the one-dimensional periodic trapezoidal estimate successively in
those two coordinates.  The resulting deterministic error is `O(N⁻²)`.

Periodicity at both coordinate endpoints, the fibrewise `C²` bound in the
second coordinate, and the `C²` bound for the second-coordinate marginal in
the first coordinate are all explicit hypotheses.  A final corollary permits
time-dependent curvature bounds and a joint volume/time schedule.  No
kinetic equation is assumed.
-/

namespace ArchonPhysics.PeriodicFourierGridTensorQuadrature

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open ArchonPhysics.PeriodicFourierGridQuadrature
open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

/-- Nested normalized sum over the two free periodic Fourier momenta. -/
def periodicFourierTensorGridQuadrature
    (N : Nat) [NeZero N] (F : Real → Real → Real) : Real :=
  (2 * Real.pi / (N : Real)) *
    ∑ k₁ : Site N,
      (2 * Real.pi / (N : Real)) *
        ∑ k₂ : Site N, F (gridWaveNumber N k₁) (gridWaveNumber N k₂)

/-- Iterated continuum integral over the Brillouin torus. -/
def periodicFourierTensorIntervalIntegral
    (F : Real → Real → Real) : Real :=
  ∫ x in (0 : Real)..(2 * Real.pi),
    ∫ y in (0 : Real)..(2 * Real.pi), F x y

/-- Marginal obtained after integrating the second free momentum. -/
def secondCoordinateIntervalMarginal
    (F : Real → Real → Real) (x : Real) : Real :=
  ∫ y in (0 : Real)..(2 * Real.pi), F x y

/-- Tensor-product periodic trapezoidal estimate.  The first term is the
accumulated second-coordinate error over an interval of length `2π`; the
second is the quadrature error of the integrated first-coordinate marginal. -/
theorem abs_periodicFourierTensorGridQuadrature_sub_integral_le
    (N : Nat) [NeZero N] (F : Real → Real → Real)
    (hendpoint₂ : ∀ x, F x 0 = F x (2 * Real.pi))
    (hC2₂ : ∀ x, ContDiffOn Real 2 (fun y ↦ F x y)
      (uIcc (0 : Real) (2 * Real.pi)))
    {zeta₂ : Real}
    (hsecond₂ : ∀ x y,
      |iteratedDerivWithin 2 (fun z ↦ F x z)
        (uIcc (0 : Real) (2 * Real.pi)) y| ≤ zeta₂)
    (hendpoint₁ : ∀ y, F 0 y = F (2 * Real.pi) y)
    (hC2₁Marginal : ContDiffOn Real 2
      (secondCoordinateIntervalMarginal F)
      (uIcc (0 : Real) (2 * Real.pi)))
    {zeta₁ : Real}
    (hsecond₁Marginal : ∀ x,
      |iteratedDerivWithin 2 (secondCoordinateIntervalMarginal F)
        (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta₁) :
    |periodicFourierTensorGridQuadrature N F -
      periodicFourierTensorIntervalIntegral F| ≤
      (2 * Real.pi) *
        (|2 * Real.pi - 0| ^ 3 * zeta₂ / (12 * (N : Real) ^ 2)) +
      |2 * Real.pi - 0| ^ 3 * zeta₁ / (12 * (N : Real) ^ 2) := by
  let L : Real := 2 * Real.pi
  let step : Real := L / (N : Real)
  let marginal : Real → Real := secondCoordinateIntervalMarginal F
  let fibreGrid : Real → Real := fun x ↦
    step * ∑ k₂ : Site N, F x (gridWaveNumber N k₂)
  let error₂ : Real := |L - 0| ^ 3 * zeta₂ / (12 * (N : Real) ^ 2)
  let error₁ : Real := |L - 0| ^ 3 * zeta₁ / (12 * (N : Real) ^ 2)
  have hNpos : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hstepPos : 0 < step := by
    dsimp [step, L]
    positivity
  have hzeta₂ : 0 ≤ zeta₂ :=
    (abs_nonneg (iteratedDerivWithin 2 (fun z ↦ F 0 z)
      (uIcc (0 : Real) (2 * Real.pi)) 0)).trans
        (hsecond₂ 0 0)
  have herror₂ : 0 ≤ error₂ := by
    dsimp [error₂, L]
    positivity
  have hfibreError (x : Real) :
      |fibreGrid x - marginal x| ≤ error₂ := by
    simpa [fibreGrid, marginal, step, error₂, L,
      secondCoordinateIntervalMarginal] using
      (abs_fourierGrid_sum_sub_integral_le N (fun y ↦ F x y)
        (hendpoint₂ x) (hC2₂ x) (hsecond₂ x))
  have hmarginalEndpoint : marginal 0 = marginal L := by
    dsimp [marginal, secondCoordinateIntervalMarginal, L]
    apply intervalIntegral.integral_congr
    intro y _hy
    exact hendpoint₁ y
  have hmarginalError :
      |step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
        ∫ x in (0 : Real)..L, marginal x| ≤ error₁ := by
    simpa [step, L, marginal, error₁] using
      (abs_fourierGrid_sum_sub_integral_le N marginal
        hmarginalEndpoint hC2₁Marginal hsecond₁Marginal)
  have hfibreTotal :
      |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
        step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)| ≤
          L * error₂ := by
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
      _ = L * error₂ := by
        rw [abs_of_pos hstepPos]
        simp only [Finset.sum_const, Finset.card_univ, ZMod.card,
          nsmul_eq_mul]
        dsimp [step]
        field_simp [ne_of_gt hNpos]
  change
    |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
      ∫ x in (0 : Real)..L, marginal x| ≤ L * error₂ + error₁
  calc
    |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
        ∫ x in (0 : Real)..L, marginal x| ≤
        |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
          step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)| +
        |step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
          ∫ x in (0 : Real)..L, marginal x| := by
      calc
        |step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
            ∫ x in (0 : Real)..L, marginal x| =
            |(step * ∑ k₁ : Site N, fibreGrid (gridWaveNumber N k₁) -
              step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁)) +
             (step * ∑ k₁ : Site N, marginal (gridWaveNumber N k₁) -
              ∫ x in (0 : Real)..L, marginal x)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    _ ≤ L * error₂ + error₁ :=
      add_le_add hfibreTotal hmarginalError

/-! ## Joint volume/time scaling -/

/-- If the combined time-dependent curvature divided by `N²` tends to
zero along `N=n+1`, then the two-dimensional discrete-to-continuum
quadrature error tends to zero. -/
theorem periodicFourierTensorQuadratureError_tendsto_zero
    (F : Nat → Real → Real → Real)
    (zeta₁ zeta₂ : Nat → Real)
    (hendpoint₂ : ∀ n x, F n x 0 = F n x (2 * Real.pi))
    (hC2₂ : ∀ n x, ContDiffOn Real 2 (fun y ↦ F n x y)
      (uIcc (0 : Real) (2 * Real.pi)))
    (hsecond₂ : ∀ n x y,
      |iteratedDerivWithin 2 (fun z ↦ F n x z)
        (uIcc (0 : Real) (2 * Real.pi)) y| ≤ zeta₂ n)
    (hendpoint₁ : ∀ n y, F n 0 y = F n (2 * Real.pi) y)
    (hC2₁Marginal : ∀ n, ContDiffOn Real 2
      (secondCoordinateIntervalMarginal (F n))
      (uIcc (0 : Real) (2 * Real.pi)))
    (hsecond₁Marginal : ∀ n x,
      |iteratedDerivWithin 2 (secondCoordinateIntervalMarginal (F n))
        (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta₁ n)
    (hcurvatureScale : Tendsto
      (fun n : Nat ↦
        ((2 * Real.pi) * zeta₂ n + zeta₁ n) /
          (((n + 1 : Nat) : Real) ^ 2)) atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        |periodicFourierTensorGridQuadrature (n + 1) (F n) -
          periodicFourierTensorIntervalIntegral (F n)|)
      atTop (nhds 0) := by
  let constant : Real := |2 * Real.pi - 0| ^ 3 / 12
  have hupper : Tendsto
      (fun n : Nat ↦ constant *
        (((2 * Real.pi) * zeta₂ n + zeta₁ n) /
          (((n + 1 : Nat) : Real) ^ 2))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hcurvatureScale
  apply squeeze_zero' (g := fun n : Nat ↦ constant *
    (((2 * Real.pi) * zeta₂ n + zeta₁ n) /
      (((n + 1 : Nat) : Real) ^ 2)))
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      have hbound :=
        abs_periodicFourierTensorGridQuadrature_sub_integral_le
          (n + 1) (F n) (hendpoint₂ n) (hC2₂ n) (hsecond₂ n)
          (hendpoint₁ n) (hC2₁Marginal n) (hsecond₁Marginal n)
      refine hbound.trans_eq ?_
      dsimp [constant]
      ring
  · exact hupper

end

end ArchonPhysics.PeriodicFourierGridTensorQuadrature

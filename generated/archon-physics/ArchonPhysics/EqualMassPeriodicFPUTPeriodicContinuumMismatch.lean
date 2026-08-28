import ArchonPhysics.FPUTFiniteTimeCollisionQuadrature

/-!
# A globally periodic continuum mismatch for equal-mass FPUT

The direct and Umklapp formulas are local analytic charts of one periodic
dispersion.  For quadrature it is cleaner to use the global frequency
`|2 sin(k/2)|`.  This module proves that its reduced four-wave mismatch is
continuous, `2π`-periodic, two-Lipschitz in the free momentum, and agrees
exactly with the finite `ZMod N` mismatch at every Fourier grid point.

Combining these facts with the finite-time resonance-kernel estimate gives
an explicit collision-slice discretization error whose long-time cost is
`O(T²/N)` for uniformly controlled marks.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open Set
open scoped BigOperators

noncomputable section

/-- Global `2π`-periodic acoustic frequency. -/
def periodicContinuumAcousticFrequency (k : Real) : Real :=
  |continuumAcousticFrequency k|

theorem continuous_periodicContinuumAcousticFrequency :
    Continuous periodicContinuumAcousticFrequency := by
  unfold periodicContinuumAcousticFrequency continuumAcousticFrequency
  fun_prop

@[simp] theorem periodicContinuumAcousticFrequency_add_two_pi (k : Real) :
    periodicContinuumAcousticFrequency (k + 2 * Real.pi) =
      periodicContinuumAcousticFrequency k := by
  unfold periodicContinuumAcousticFrequency
  rw [continuumAcousticFrequency_add_two_pi, abs_neg]

@[simp] theorem periodicContinuumAcousticFrequency_sub_two_pi (k : Real) :
    periodicContinuumAcousticFrequency (k - 2 * Real.pi) =
      periodicContinuumAcousticFrequency k := by
  unfold periodicContinuumAcousticFrequency
  rw [continuumAcousticFrequency_sub_two_pi, abs_neg]

/-- The periodic acoustic frequency is globally one-Lipschitz. -/
theorem abs_periodicContinuumAcousticFrequency_sub_le (x y : Real) :
    |periodicContinuumAcousticFrequency x -
        periodicContinuumAcousticFrequency y| ≤ |x - y| := by
  have hbase : |continuumAcousticFrequency x -
      continuumAcousticFrequency y| ≤ |x - y| := by
    unfold continuumAcousticFrequency
    calc
      |2 * Real.sin (x / 2) - 2 * Real.sin (y / 2)| =
          2 * |Real.sin (x / 2) - Real.sin (y / 2)| := by
            rw [← mul_sub, abs_mul]
            norm_num
      _ ≤ 2 * |x / 2 - y / 2| :=
        mul_le_mul_of_nonneg_left
          (Real.abs_sin_sub_sin_le (x / 2) (y / 2)) (by norm_num)
      _ = |x - y| := by
        rw [← sub_div, abs_div]
        norm_num
        ring
  unfold periodicContinuumAcousticFrequency
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans hbase

/-- The global periodic continuum frequency samples the exact finite FPUT
frequency on the principal Fourier grid. -/
theorem periodicContinuumAcousticFrequency_gridWaveNumber
    (N : Nat) [NeZero N] (k : Site N) :
    periodicContinuumAcousticFrequency (gridWaveNumber N k) =
      periodicSineFrequency N k := by
  unfold periodicContinuumAcousticFrequency
  rw [continuumAcousticFrequency_gridWaveNumber]
  exact abs_of_nonneg (periodicSineFrequency_nonneg N k)

/-- The periodic continuum frequency of the raw eliminated momentum agrees
with that of its finite `ZMod N` representative. -/
theorem periodicContinuumAcousticFrequency_rawFourth_eq_gridFourth
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    periodicContinuumAcousticFrequency
        (gridWaveNumber N k₀ + gridWaveNumber N k₁ -
          gridWaveNumber N k₂) =
      periodicContinuumAcousticFrequency
        (gridWaveNumber N (k₀ + k₁ - k₂)) := by
  let raw := gridWaveNumber N k₀ + gridWaveNumber N k₁ -
    gridWaveNumber N k₂
  rcases grid_fourth_eq_direct_or_one_wrap k₀ k₁ k₂ with
    hdirect | hadd | hsub
  · change periodicContinuumAcousticFrequency raw = _
    rw [hdirect]
  · change periodicContinuumAcousticFrequency raw = _
    rw [hadd, periodicContinuumAcousticFrequency_add_two_pi]
  · change periodicContinuumAcousticFrequency raw = _
    rw [hsub, periodicContinuumAcousticFrequency_sub_two_pi]

/-- Global periodic reduced `2 ↔ 2` mismatch. -/
def periodicReducedFourWaveMismatch (k₀ k₁ k₂ : Real) : Real :=
  periodicContinuumAcousticFrequency k₀ +
    periodicContinuumAcousticFrequency k₁ -
      periodicContinuumAcousticFrequency k₂ -
        periodicContinuumAcousticFrequency (k₀ + k₁ - k₂)

theorem continuous_periodicReducedFourWaveMismatch_k₂ (k₀ k₁ : Real) :
    Continuous (fun k₂ ↦ periodicReducedFourWaveMismatch k₀ k₁ k₂) := by
  unfold periodicReducedFourWaveMismatch
  apply Continuous.sub
  · apply Continuous.sub
    · exact continuous_const.add continuous_const
    · exact continuous_periodicContinuumAcousticFrequency
  · exact continuous_periodicContinuumAcousticFrequency.comp (by fun_prop)

@[simp] theorem periodicReducedFourWaveMismatch_k₂_add_two_pi
    (k₀ k₁ k₂ : Real) :
    periodicReducedFourWaveMismatch k₀ k₁ (k₂ + 2 * Real.pi) =
      periodicReducedFourWaveMismatch k₀ k₁ k₂ := by
  unfold periodicReducedFourWaveMismatch
  rw [periodicContinuumAcousticFrequency_add_two_pi]
  have hraw : k₀ + k₁ - (k₂ + 2 * Real.pi) =
      (k₀ + k₁ - k₂) - 2 * Real.pi := by ring
  rw [hraw, periodicContinuumAcousticFrequency_sub_two_pi]

@[simp] theorem periodicReducedFourWaveMismatch_k₂_endpoint
    (k₀ k₁ : Real) :
    periodicReducedFourWaveMismatch k₀ k₁ 0 =
      periodicReducedFourWaveMismatch k₀ k₁ (2 * Real.pi) := by
  simpa using
    (periodicReducedFourWaveMismatch_k₂_add_two_pi k₀ k₁ 0).symm

/-- The global reduced mismatch is two-Lipschitz in its free momentum. -/
theorem abs_periodicReducedFourWaveMismatch_sub_le
    (k₀ k₁ x y : Real) :
    |periodicReducedFourWaveMismatch k₀ k₁ x -
        periodicReducedFourWaveMismatch k₀ k₁ y| ≤
      2 * |x - y| := by
  let omega := periodicContinuumAcousticFrequency
  have hx := abs_periodicContinuumAcousticFrequency_sub_le y x
  have hraw := abs_periodicContinuumAcousticFrequency_sub_le
    (k₀ + k₁ - y) (k₀ + k₁ - x)
  unfold periodicReducedFourWaveMismatch
  change |omega k₀ + omega k₁ - omega x -
      omega (k₀ + k₁ - x) -
      (omega k₀ + omega k₁ - omega y -
        omega (k₀ + k₁ - y))| ≤ _
  calc
    |omega k₀ + omega k₁ - omega x -
        omega (k₀ + k₁ - x) -
        (omega k₀ + omega k₁ - omega y -
          omega (k₀ + k₁ - y))| =
        |(omega y - omega x) +
          (omega (k₀ + k₁ - y) -
            omega (k₀ + k₁ - x))| := by
      congr 1
      ring
    _ ≤ |omega y - omega x| +
        |omega (k₀ + k₁ - y) -
          omega (k₀ + k₁ - x)| := abs_add_le _ _
    _ ≤ |y - x| +
        |(k₀ + k₁ - y) - (k₀ + k₁ - x)| :=
      add_le_add hx hraw
    _ = 2 * |x - y| := by
      rw [abs_sub_comm y x]
      have : (k₀ + k₁ - y) - (k₀ + k₁ - x) = x - y := by ring
      rw [this]
      ring

/-- Exact finite-grid sampling identity for the global periodic mismatch. -/
theorem periodicReducedFourWaveMismatch_grid_eq
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    periodicReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (gridWaveNumber N k₂) =
      reducedTwoToTwoMismatch k₀ k₁ k₂ := by
  unfold periodicReducedFourWaveMismatch reducedTwoToTwoMismatch
  rw [periodicContinuumAcousticFrequency_gridWaveNumber,
    periodicContinuumAcousticFrequency_gridWaveNumber,
    periodicContinuumAcousticFrequency_gridWaveNumber,
    periodicContinuumAcousticFrequency_rawFourth_eq_gridFourth,
    periodicContinuumAcousticFrequency_gridWaveNumber]

/-- Actual fixed-`k₀,k₁` finite collision slice versus its global periodic
continuum integral.  Only regularity of the supplied physical mark remains
as an input; the FPUT mismatch slope is discharged with the exact constant
two. -/
theorem abs_actualFPUTCollisionSlice_sub_continuum_le
    (N : Nat) [NeZero N] (k₀ k₁ : Site N)
    (mark : Real → Real) {T markBound markSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope)
    (hmarkContinuous : Continuous mark)
    (hmarkEndpoint : mark 0 = mark (2 * Real.pi))
    (hmarkBoundOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mark x - mark y| ≤ markSlope * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k₂ : Site N, mark (gridWaveNumber N k₂) *
          normalizedFiniteTimeResonanceKernel
            (reducedTwoToTwoMismatch k₀ k₁ k₂) T -
      ∫ x in (0 : Real)..(2 * Real.pi),
        finiteTimeMarkedCollisionIntegrand
          (periodicReducedFourWaveMismatch
            (gridWaveNumber N k₀) (gridWaveNumber N k₁)) mark T x| ≤
      finiteTimeMarkedCollisionLipschitzConstant
          T markBound markSlope 2 *
        (2 * Real.pi) ^ 2 / (N : Real) := by
  have hbound :=
    abs_finiteTimeMarkedCollision_fourierGrid_sub_integral_le
      N
      (periodicReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁))
      mark hT hmarkBound hmarkSlope (by norm_num : (0 : Real) ≤ 2)
      hmarkContinuous
      (continuous_periodicReducedFourWaveMismatch_k₂ _ _)
      hmarkEndpoint
      (periodicReducedFourWaveMismatch_k₂_endpoint _ _)
      hmarkBoundOn hmarkLipOn
      (fun x _hx y _hy ↦
        abs_periodicReducedFourWaveMismatch_sub_le _ _ x y)
  simpa only [finiteTimeMarkedCollisionIntegrand,
    periodicReducedFourWaveMismatch_grid_eq] using hbound

end

end ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch

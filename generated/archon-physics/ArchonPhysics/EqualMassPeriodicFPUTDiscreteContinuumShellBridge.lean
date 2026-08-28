import ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

/-!
# Discrete-to-continuum bridge for the equal-mass FPUT four-wave shell

The finite Fourier label `k : ZMod N` is embedded in the principal
Brillouin interval by `κ_N(k) = 2π k.val / N`.  This module proves that the
finite acoustic frequency is exactly the continuum sine frequency on this
grid and classifies the eliminated fourth momentum into three possibilities:
no wrap, a lower wrap by `+2π`, or an upper wrap by `-2π`.

Consequently every finite reduced `2 ↔ 2` mismatch is exactly either the
direct continuum mismatch or the one-wrap Umklapp mismatch at grid points.
This is an identity, not yet a Riemann-sum or kinetic-limit theorem.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.Lattice

noncomputable section

/-- Principal-zone continuum wave number of one finite Fourier mode. -/
def gridWaveNumber (N : Nat) [NeZero N] (k : Site N) : Real :=
  2 * Real.pi * (k.val : Real) / (N : Real)

/-- The finite sine dispersion is literally the continuum dispersion sampled
on the Fourier grid. -/
theorem continuumAcousticFrequency_gridWaveNumber
    (N : Nat) [NeZero N] (k : Site N) :
    continuumAcousticFrequency (gridWaveNumber N k) =
      periodicSineFrequency N k := by
  unfold continuumAcousticFrequency gridWaveNumber periodicSineFrequency
  congr 2
  ring

theorem continuumAcousticFrequency_add_two_pi (k : Real) :
    continuumAcousticFrequency (k + 2 * Real.pi) =
      -continuumAcousticFrequency k := by
  unfold continuumAcousticFrequency
  rw [show (k + 2 * Real.pi) / 2 = k / 2 + Real.pi by ring,
    Real.sin_add_pi]
  ring

theorem continuumAcousticFrequency_sub_two_pi (k : Real) :
    continuumAcousticFrequency (k - 2 * Real.pi) =
      -continuumAcousticFrequency k := by
  unfold continuumAcousticFrequency
  rw [show (k - 2 * Real.pi) / 2 = k / 2 - Real.pi by ring,
    Real.sin_sub_pi]
  ring

/-- Direct/no-wrap grid relation implies the direct continuum mismatch. -/
theorem reducedTwoToTwoMismatch_eq_direct_of_grid_eq
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hgrid : gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ =
      directReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (gridWaveNumber N k₂) := by
  unfold reducedTwoToTwoMismatch directReducedFourWaveMismatch
  rw [← continuumAcousticFrequency_gridWaveNumber N k₀,
    ← continuumAcousticFrequency_gridWaveNumber N k₁,
    ← continuumAcousticFrequency_gridWaveNumber N k₂,
    ← continuumAcousticFrequency_gridWaveNumber N (k₀ + k₁ - k₂),
    hgrid]

/-- A lower `+2π` wrap gives the Umklapp analytic branch. -/
theorem reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_add_two_pi
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hgrid : gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ +
        2 * Real.pi) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ =
      umklappReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (gridWaveNumber N k₂) := by
  unfold reducedTwoToTwoMismatch umklappReducedFourWaveMismatch
  rw [← continuumAcousticFrequency_gridWaveNumber N k₀,
    ← continuumAcousticFrequency_gridWaveNumber N k₁,
    ← continuumAcousticFrequency_gridWaveNumber N k₂,
    ← continuumAcousticFrequency_gridWaveNumber N (k₀ + k₁ - k₂),
    hgrid, continuumAcousticFrequency_add_two_pi]
  ring

/-- An upper `-2π` wrap gives the same Umklapp analytic branch. -/
theorem reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_sub_two_pi
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hgrid : gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ -
        2 * Real.pi) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ =
      umklappReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (gridWaveNumber N k₂) := by
  unfold reducedTwoToTwoMismatch umklappReducedFourWaveMismatch
  rw [← continuumAcousticFrequency_gridWaveNumber N k₀,
    ← continuumAcousticFrequency_gridWaveNumber N k₁,
    ← continuumAcousticFrequency_gridWaveNumber N k₂,
    ← continuumAcousticFrequency_gridWaveNumber N (k₀ + k₁ - k₂),
    hgrid, continuumAcousticFrequency_sub_two_pi]
  ring

private theorem gridWaveNumber_eq_of_val_eq
    {N : Nat} [NeZero N] {k : Site N} {value : Nat}
    (hval : k.val = value) :
    gridWaveNumber N k = 2 * Real.pi * (value : Real) / (N : Real) := by
  simp [gridWaveNumber, hval]

/-- No wrap when the integer sum is below `N` and `k₂` does not exceed it. -/
theorem grid_fourth_eq_direct_of_sum_lt_of_le
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hsum : k₀.val + k₁.val < N)
    (hk₂ : k₂.val ≤ k₀.val + k₁.val) :
    gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ := by
  have hadd : (k₀ + k₁).val = k₀.val + k₁.val :=
    ZMod.val_add_of_lt hsum
  have hsub : (k₀ + k₁ - k₂).val =
      k₀.val + k₁.val - k₂.val := by
    rw [ZMod.val_sub (by simpa [hadd] using hk₂), hadd]
  rw [gridWaveNumber_eq_of_val_eq hsub]
  unfold gridWaveNumber
  rw [Nat.cast_sub hk₂]
  push_cast
  ring

/-- Lower wrap when the integer sum is below `N` but `k₂` exceeds it. -/
theorem grid_fourth_eq_add_two_pi_of_sum_lt_of_lt
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hsum : k₀.val + k₁.val < N)
    (hk₂ : k₀.val + k₁.val < k₂.val) :
    gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ +
        2 * Real.pi := by
  have hadd : (k₀ + k₁).val = k₀.val + k₁.val :=
    ZMod.val_add_of_lt hsum
  have hk₂ne : k₂ ≠ 0 := by
    intro hzero
    subst k₂
    simp at hk₂
  have hneg : (-k₂).val = N - k₂.val := by
    simp [ZMod.neg_val k₂, hk₂ne]
  have hk₂N : k₂.val < N := k₂.val_lt
  have hsumNeg : (k₀ + k₁).val + (-k₂).val < N := by
    rw [hadd, hneg]
    omega
  have hval : (k₀ + k₁ - k₂).val =
      k₀.val + k₁.val + N - k₂.val := by
    rw [sub_eq_add_neg, ZMod.val_add_of_lt hsumNeg, hadd, hneg]
    exact (Nat.add_sub_assoc (Nat.le_of_lt hk₂N)
      (k₀.val + k₁.val)).symm
  rw [gridWaveNumber_eq_of_val_eq hval]
  unfold gridWaveNumber
  rw [Nat.cast_sub (by omega : k₂.val ≤ k₀.val + k₁.val + N)]
  push_cast
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp
  ring

/-- Upper wrap when the raw integer fourth mode is at least `N`. -/
theorem grid_fourth_eq_sub_two_pi_of_sum_le_of_le
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N)
    (hsum : N ≤ k₀.val + k₁.val)
    (hk₂ : k₂.val ≤ k₀.val + k₁.val - N) :
    gridWaveNumber N (k₀ + k₁ - k₂) =
      gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ -
        2 * Real.pi := by
  have hadd : (k₀ + k₁).val = k₀.val + k₁.val - N :=
    ZMod.val_add_of_le hsum
  have hval : (k₀ + k₁ - k₂).val =
      (k₀.val + k₁.val - N) - k₂.val := by
    rw [ZMod.val_sub (by simpa [hadd] using hk₂), hadd]
  rw [gridWaveNumber_eq_of_val_eq hval]
  unfold gridWaveNumber
  rw [Nat.cast_sub hk₂, Nat.cast_sub hsum]
  push_cast
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp
  ring

/-- The fourth grid mode is always the raw real sum, shifted by at most one
Brillouin period. -/
theorem grid_fourth_eq_direct_or_one_wrap
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    gridWaveNumber N (k₀ + k₁ - k₂) =
        gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ ∨
      gridWaveNumber N (k₀ + k₁ - k₂) =
        gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ +
          2 * Real.pi ∨
      gridWaveNumber N (k₀ + k₁ - k₂) =
        gridWaveNumber N k₀ + gridWaveNumber N k₁ - gridWaveNumber N k₂ -
          2 * Real.pi := by
  by_cases hsum : k₀.val + k₁.val < N
  · by_cases hk₂ : k₂.val ≤ k₀.val + k₁.val
    · exact Or.inl (grid_fourth_eq_direct_of_sum_lt_of_le
        k₀ k₁ k₂ hsum hk₂)
    · exact Or.inr (Or.inl (grid_fourth_eq_add_two_pi_of_sum_lt_of_lt
        k₀ k₁ k₂ hsum (Nat.lt_of_not_ge hk₂)))
  · have hsum' : N ≤ k₀.val + k₁.val := Nat.le_of_not_gt hsum
    by_cases hk₂ : k₂.val ≤ k₀.val + k₁.val - N
    · exact Or.inr (Or.inr (grid_fourth_eq_sub_two_pi_of_sum_le_of_le
        k₀ k₁ k₂ hsum' hk₂))
    · left
      have hadd : (k₀ + k₁).val = k₀.val + k₁.val - N :=
        ZMod.val_add_of_le hsum'
      have hk₂lt : (k₀ + k₁).val < k₂.val := by
        simpa [hadd] using Nat.lt_of_not_ge hk₂
      have hk₂ne : k₂ ≠ 0 := by
        intro hzero
        subst k₂
        simp at hk₂lt
      have hneg : (-k₂).val = N - k₂.val := by
        simp [ZMod.neg_val k₂, hk₂ne]
      have hk₂N : k₂.val < N := k₂.val_lt
      have hsumNeg : (k₀ + k₁).val + (-k₂).val < N := by
        rw [hadd, hneg]
        omega
      have hval : (k₀ + k₁ - k₂).val =
          k₀.val + k₁.val - k₂.val := by
        rw [sub_eq_add_neg, ZMod.val_add_of_lt hsumNeg, hadd, hneg]
        omega
      rw [gridWaveNumber_eq_of_val_eq hval]
      unfold gridWaveNumber
      rw [Nat.cast_sub (by omega : k₂.val ≤ k₀.val + k₁.val)]
      push_cast
      ring

/-- Every finite-grid reduced mismatch lands exactly on the direct or
Umklapp continuum analytic branch. -/
theorem reducedTwoToTwoMismatch_eq_direct_or_umklapp
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    reducedTwoToTwoMismatch k₀ k₁ k₂ =
        directReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) ∨
      reducedTwoToTwoMismatch k₀ k₁ k₂ =
        umklappReducedFourWaveMismatch
          (gridWaveNumber N k₀) (gridWaveNumber N k₁)
            (gridWaveNumber N k₂) := by
  rcases grid_fourth_eq_direct_or_one_wrap k₀ k₁ k₂ with
    hdirect | hlower | hupper
  · exact Or.inl (reducedTwoToTwoMismatch_eq_direct_of_grid_eq
      k₀ k₁ k₂ hdirect)
  · exact Or.inr (reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_add_two_pi
      k₀ k₁ k₂ hlower)
  · exact Or.inr (reducedTwoToTwoMismatch_eq_umklapp_of_grid_eq_sub_two_pi
      k₀ k₁ k₂ hupper)

end

end ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge

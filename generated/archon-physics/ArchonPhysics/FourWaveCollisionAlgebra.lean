import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Algebra of one resonant four-wave collision

The first normal-form reduction of equal-mass alpha-FPUT produces an
effective quartic Hamiltonian interaction.  This module records the exact
`2 <-> 2` wave-kinetic algebra for one supplied resonant quartet: action and
dispersion-energy conservation, nonnegative logarithmic entropy production,
and Rayleigh--Jeans detailed balance.

It does not identify the effective rate from the microscopic Hamiltonian and
does not assert the large-volume diagram limit.
-/

namespace ArchonPhysics.FourWaveCollisionAlgebra

noncomputable section

/-- Inverse-action mismatch for `1 + 2 <-> 3 + 4`. -/
def fourWaveInverseActionMismatch (n₁ n₂ n₃ n₄ : Real) : Real :=
  n₁⁻¹ + n₂⁻¹ - n₃⁻¹ - n₄⁻¹

/-- Classical four-wave gain-loss flux in detailed-balance form. -/
def fourWaveCollisionFlux (n₁ n₂ n₃ n₄ : Real) : Real :=
  n₁ * n₂ * n₃ * n₄ * fourWaveInverseActionMismatch n₁ n₂ n₃ n₄

/-- Slope of a weighted observable along `(+,+,-,-)`. -/
def fourWaveLinearObservableSlope
    (γ₁ γ₂ γ₃ γ₄ rate n₁ n₂ n₃ n₄ : Real) : Real :=
  rate * fourWaveCollisionFlux n₁ n₂ n₃ n₄ * (γ₁ + γ₂ - γ₃ - γ₄)

/-- Logarithmic entropy production for one quartet. -/
def fourWaveEntropyProduction (rate n₁ n₂ n₃ n₄ : Real) : Real :=
  rate * fourWaveCollisionFlux n₁ n₂ n₃ n₄ *
    fourWaveInverseActionMismatch n₁ n₂ n₃ n₄

theorem fourWaveLinearObservableSlope_eq_zero_of_balance
    (γ₁ γ₂ γ₃ γ₄ rate n₁ n₂ n₃ n₄ : Real)
    (hγ : γ₁ + γ₂ = γ₃ + γ₄) :
    fourWaveLinearObservableSlope
      γ₁ γ₂ γ₃ γ₄ rate n₁ n₂ n₃ n₄ = 0 := by
  unfold fourWaveLinearObservableSlope
  rw [hγ]
  ring

/-- Every `2 <-> 2` quartet conserves wave action. -/
theorem fourWaveActionSlope_eq_zero
    (rate n₁ n₂ n₃ n₄ : Real) :
    fourWaveLinearObservableSlope 1 1 1 1 rate n₁ n₂ n₃ n₄ = 0 := by
  apply fourWaveLinearObservableSlope_eq_zero_of_balance
  norm_num

/-- An on-shell quartet conserves dispersion energy. -/
theorem fourWaveEnergySlope_eq_zero_of_resonance
    (ω₁ ω₂ ω₃ ω₄ rate n₁ n₂ n₃ n₄ : Real)
    (hω : ω₁ + ω₂ = ω₃ + ω₄) :
    fourWaveLinearObservableSlope
      ω₁ ω₂ ω₃ ω₄ rate n₁ n₂ n₃ n₄ = 0 :=
  fourWaveLinearObservableSlope_eq_zero_of_balance
    ω₁ ω₂ ω₃ ω₄ rate n₁ n₂ n₃ n₄ hω

theorem fourWaveEntropyProduction_eq_weighted_square
    (rate n₁ n₂ n₃ n₄ : Real) :
    fourWaveEntropyProduction rate n₁ n₂ n₃ n₄ =
      rate * (n₁ * n₂ * n₃ * n₄) *
        (fourWaveInverseActionMismatch n₁ n₂ n₃ n₄) ^ 2 := by
  unfold fourWaveEntropyProduction fourWaveCollisionFlux
  ring

theorem fourWaveEntropyProduction_nonneg
    {rate n₁ n₂ n₃ n₄ : Real}
    (hrate : 0 ≤ rate)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hn₃ : 0 < n₃) (hn₄ : 0 < n₄) :
    0 ≤ fourWaveEntropyProduction rate n₁ n₂ n₃ n₄ := by
  rw [fourWaveEntropyProduction_eq_weighted_square]
  positivity

/-- Rayleigh--Jeans profile for four-wave action. -/
def fourWaveRayleighJeansAction
    (chemical inverseTemperature frequency : Real) : Real :=
  (chemical + inverseTemperature * frequency)⁻¹

/-- Affine inverse action satisfies detailed balance on every resonant
quartet. -/
theorem fourWaveInverseActionMismatch_rayleighJeans_eq_zero
    (chemical inverseTemperature : Real) (ω₁ ω₂ ω₃ ω₄ : Real)
    (hω : ω₁ + ω₂ = ω₃ + ω₄) :
    fourWaveInverseActionMismatch
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₁)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₂)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₃)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₄) = 0 := by
  unfold fourWaveInverseActionMismatch fourWaveRayleighJeansAction
  simp only [inv_inv]
  linear_combination inverseTemperature * hω

theorem fourWaveCollisionFlux_rayleighJeans_eq_zero
    (chemical inverseTemperature : Real) (ω₁ ω₂ ω₃ ω₄ : Real)
    (hω : ω₁ + ω₂ = ω₃ + ω₄) :
    fourWaveCollisionFlux
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₁)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₂)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₃)
      (fourWaveRayleighJeansAction chemical inverseTemperature ω₄) = 0 := by
  unfold fourWaveCollisionFlux
  rw [fourWaveInverseActionMismatch_rayleighJeans_eq_zero
    chemical inverseTemperature ω₁ ω₂ ω₃ ω₄ hω]
  ring

end

end ArchonPhysics.FourWaveCollisionAlgebra

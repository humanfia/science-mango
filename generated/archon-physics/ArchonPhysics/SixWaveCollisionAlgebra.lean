import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Algebra of one resonant six-wave collision

For equal-mass periodic alpha-FPUT, the first finite-volume resonant network
capable of connecting the spectrum is a `3 <-> 3` six-wave channel.  This
module records the exact pointwise collision algebra for one supplied
sextet.  It proves the collision invariants, logarithmic entropy production,
and Rayleigh--Jeans detailed balance.

These are consequences of a supplied six-wave collision rate.  The module
does not derive that rate from the Hamiltonian and does not assert a kinetic
limit or thermalization.
-/

namespace ArchonPhysics.SixWaveCollisionAlgebra

noncomputable section

/-- The inverse-action mismatch for the signed reaction
`1 + 2 + 3 <-> 4 + 5 + 6`. -/
def sixWaveInverseActionMismatch
    (n₁ n₂ n₃ n₄ n₅ n₆ : Real) : Real :=
  n₁⁻¹ + n₂⁻¹ + n₃⁻¹ - n₄⁻¹ - n₅⁻¹ - n₆⁻¹

/-- Classical six-wave gain-loss flux in its detailed-balance
factorization. -/
def sixWaveCollisionFlux
    (n₁ n₂ n₃ n₄ n₅ n₆ : Real) : Real :=
  n₁ * n₂ * n₃ * n₄ * n₅ * n₆ *
    sixWaveInverseActionMismatch n₁ n₂ n₃ n₄ n₅ n₆

/-- Slope of a weighted linear observable along the signed collision
direction `(+,+,+,-,-,-)`. -/
def sixWaveLinearObservableSlope
    (γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ rate n₁ n₂ n₃ n₄ n₅ n₆ : Real) : Real :=
  rate * sixWaveCollisionFlux n₁ n₂ n₃ n₄ n₅ n₆ *
    (γ₁ + γ₂ + γ₃ - γ₄ - γ₅ - γ₆)

/-- Logarithmic entropy production of one six-wave collision. -/
def sixWaveEntropyProduction
    (rate n₁ n₂ n₃ n₄ n₅ n₆ : Real) : Real :=
  rate * sixWaveCollisionFlux n₁ n₂ n₃ n₄ n₅ n₆ *
    sixWaveInverseActionMismatch n₁ n₂ n₃ n₄ n₅ n₆

/-- A signed-balanced weight is a collision invariant. -/
theorem sixWaveLinearObservableSlope_eq_zero_of_balance
    (γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ rate n₁ n₂ n₃ n₄ n₅ n₆ : Real)
    (hγ : γ₁ + γ₂ + γ₃ = γ₄ + γ₅ + γ₆) :
    sixWaveLinearObservableSlope
      γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ rate n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixWaveLinearObservableSlope
  rw [hγ]
  ring

/-- Wave action is conserved by every `3 <-> 3` channel. -/
theorem sixWaveActionSlope_eq_zero
    (rate n₁ n₂ n₃ n₄ n₅ n₆ : Real) :
    sixWaveLinearObservableSlope
      1 1 1 1 1 1 rate n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  apply sixWaveLinearObservableSlope_eq_zero_of_balance
  norm_num

/-- Dispersion energy is conserved on the six-wave resonance shell. -/
theorem sixWaveEnergySlope_eq_zero_of_resonance
    (ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ : Real)
    (hω : ω₁ + ω₂ + ω₃ = ω₄ + ω₅ + ω₆) :
    sixWaveLinearObservableSlope
      ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ = 0 :=
  sixWaveLinearObservableSlope_eq_zero_of_balance
    ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ rate n₁ n₂ n₃ n₄ n₅ n₆ hω

/-- The entropy production is a nonnegative weight times a square. -/
theorem sixWaveEntropyProduction_eq_weighted_square
    (rate n₁ n₂ n₃ n₄ n₅ n₆ : Real) :
    sixWaveEntropyProduction rate n₁ n₂ n₃ n₄ n₅ n₆ =
      rate * (n₁ * n₂ * n₃ * n₄ * n₅ * n₆) *
        (sixWaveInverseActionMismatch n₁ n₂ n₃ n₄ n₅ n₆) ^ 2 := by
  unfold sixWaveEntropyProduction sixWaveCollisionFlux
  ring

/-- Positive actions and a nonnegative collision rate give nonnegative
logarithmic entropy production. -/
theorem sixWaveEntropyProduction_nonneg
    {rate n₁ n₂ n₃ n₄ n₅ n₆ : Real}
    (hrate : 0 ≤ rate)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hn₆ : 0 < n₆) :
    0 ≤ sixWaveEntropyProduction rate n₁ n₂ n₃ n₄ n₅ n₆ := by
  rw [sixWaveEntropyProduction_eq_weighted_square]
  positivity

/-- With positive actions, detailed balance is equivalent to zero flux. -/
theorem sixWaveCollisionFlux_eq_zero_iff_mismatch_eq_zero
    {n₁ n₂ n₃ n₄ n₅ n₆ : Real}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hn₆ : 0 < n₆) :
    sixWaveCollisionFlux n₁ n₂ n₃ n₄ n₅ n₆ = 0 <->
      sixWaveInverseActionMismatch n₁ n₂ n₃ n₄ n₅ n₆ = 0 := by
  unfold sixWaveCollisionFlux
  have hproduct : n₁ * n₂ * n₃ * n₄ * n₅ * n₆ ≠ 0 := by
    positivity
  exact mul_eq_zero_iff_left hproduct

/-- Rayleigh--Jeans action profile.  Positivity is imposed separately when
the profile is used as physical data. -/
def rayleighJeansAction (chemical inverseTemperature frequency : Real) : Real :=
  (chemical + inverseTemperature * frequency)⁻¹

/-- On a `3 <-> 3` energy resonance, every affine inverse-action profile
satisfies exact detailed balance.  The chemical-potential contribution
cancels because both sides contain three waves. -/
theorem sixWaveInverseActionMismatch_rayleighJeans_eq_zero
    (chemical inverseTemperature : Real)
    (ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ : Real)
    (hω : ω₁ + ω₂ + ω₃ = ω₄ + ω₅ + ω₆) :
    sixWaveInverseActionMismatch
      (rayleighJeansAction chemical inverseTemperature ω₁)
      (rayleighJeansAction chemical inverseTemperature ω₂)
      (rayleighJeansAction chemical inverseTemperature ω₃)
      (rayleighJeansAction chemical inverseTemperature ω₄)
      (rayleighJeansAction chemical inverseTemperature ω₅)
      (rayleighJeansAction chemical inverseTemperature ω₆) = 0 := by
  unfold sixWaveInverseActionMismatch rayleighJeansAction
  simp only [inv_inv]
  linear_combination inverseTemperature * hω

/-- Consequently a Rayleigh--Jeans profile makes the collision flux vanish
on every resonant sextet. -/
theorem sixWaveCollisionFlux_rayleighJeans_eq_zero
    (chemical inverseTemperature : Real)
    (ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ : Real)
    (hω : ω₁ + ω₂ + ω₃ = ω₄ + ω₅ + ω₆) :
    sixWaveCollisionFlux
      (rayleighJeansAction chemical inverseTemperature ω₁)
      (rayleighJeansAction chemical inverseTemperature ω₂)
      (rayleighJeansAction chemical inverseTemperature ω₃)
      (rayleighJeansAction chemical inverseTemperature ω₄)
      (rayleighJeansAction chemical inverseTemperature ω₅)
      (rayleighJeansAction chemical inverseTemperature ω₆) = 0 := by
  unfold sixWaveCollisionFlux
  rw [sixWaveInverseActionMismatch_rayleighJeans_eq_zero
    chemical inverseTemperature ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ hω]
  ring

end

end ArchonPhysics.SixWaveCollisionAlgebra

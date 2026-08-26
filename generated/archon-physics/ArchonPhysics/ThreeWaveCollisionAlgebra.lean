import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Algebra of one resonant three-wave collision

This module isolates the pointwise algebra of a single `1 ↔ 2 + 3` collision.
The sign convention is the one in equation (24) of Migliorelli--Dematteis--
Chibbaro--Onorato, *Resonant interactions in the α-FPUT lattice with
site-dependent coefficients*, arXiv:2605.24268v1 (2026):

`n₂ n₃ - n₁ n₂ - n₁ n₃`.

That paper explicitly presents its wave-kinetic equation as a formal
derivation.  Its lattice has equal masses and site-dependent spring and cubic
coefficients, whereas the frozen target in this repository has random masses
and constant interaction coefficients.  Accordingly, the results below are
only unconditional real algebra for one supplied collision triad.  They do
not derive a kinetic limit, identify the frozen target's collision kernel, or
prove relaxation or thermalization.
-/

namespace ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

/-- The signed collision flux for the reaction `1 ↔ 2 + 3`. -/
def collisionFlux (n₁ n₂ n₃ : Real) : Real :=
  n₂ * n₃ - n₁ * n₂ - n₁ * n₃

/-- The inverse-action mismatch associated with `1 ↔ 2 + 3`. -/
def inverseActionMismatch (n₁ n₂ n₃ : Real) : Real :=
  n₁⁻¹ - n₂⁻¹ - n₃⁻¹

/-- The derivative of a linear observable with weights `γᵢ` along the signed
reaction direction `(+,-,-)`, with nonnegative rate prefactor `rate` in the
physical application. -/
def linearObservableSlope
    (γ₁ γ₂ γ₃ rate n₁ n₂ n₃ : Real) : Real :=
  rate * collisionFlux n₁ n₂ n₃ * (γ₁ - γ₂ - γ₃)

/-- The logarithmic entropy production of one collision triad. -/
def entropyProduction (rate n₁ n₂ n₃ : Real) : Real :=
  rate * collisionFlux n₁ n₂ n₃ * inverseActionMismatch n₁ n₂ n₃

/-- The weighted linear energy of a collision triad. -/
def triadEnergy
    (ω₁ ω₂ ω₃ n₁ n₂ n₃ : Real) : Real :=
  ω₁ * n₁ + ω₂ * n₂ + ω₃ * n₃

/-- The sum of logarithmic actions of a positive collision triad. -/
def triadLogEntropy (n₁ n₂ n₃ : Real) : Real :=
  Real.log n₁ + Real.log n₂ + Real.log n₃

/-- Exact factorization of the flux by the inverse-action mismatch. -/
theorem collisionFlux_factorization
    {n₁ n₂ n₃ : Real} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hn₃ : n₃ ≠ 0) :
    collisionFlux n₁ n₂ n₃ =
      n₁ * n₂ * n₃ * inverseActionMismatch n₁ n₂ n₃ := by
  unfold collisionFlux inverseActionMismatch
  field_simp [hn₁, hn₂, hn₃]
  all_goals ring

/-- A balanced weight `γ₁ = γ₂ + γ₃` is a collision invariant for this one
reaction, independently of the actions and rate. -/
theorem linearObservableSlope_eq_zero_of_balance
    (γ₁ γ₂ γ₃ rate n₁ n₂ n₃ : Real) (hγ : γ₁ = γ₂ + γ₃) :
    linearObservableSlope γ₁ γ₂ γ₃ rate n₁ n₂ n₃ = 0 := by
  unfold linearObservableSlope
  rw [hγ]
  ring

/-- For an active collision, vanishing of a linear observable's slope is
equivalent to the usual additive collision-invariant relation. -/
theorem linearObservableSlope_eq_zero_iff_balance
    (γ₁ γ₂ γ₃ rate n₁ n₂ n₃ : Real)
    (hrate : rate ≠ 0) (hflux : collisionFlux n₁ n₂ n₃ ≠ 0) :
    linearObservableSlope γ₁ γ₂ γ₃ rate n₁ n₂ n₃ = 0 ↔
      γ₁ = γ₂ + γ₃ := by
  unfold linearObservableSlope
  constructor
  · intro h
    have hbalance : γ₁ - γ₂ - γ₃ = 0 := by
      exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hrate hflux)
    linarith
  · intro h
    rw [h]
    ring

/-- Under the resonance relation `ω₁ = ω₂ + ω₃`, the reaction direction
`(+,-,-)` has zero weighted energy derivative. -/
theorem weightedEnergySlope_eq_zero_of_resonance
    (ω₁ ω₂ ω₃ rate n₁ n₂ n₃ : Real) (hω : ω₁ = ω₂ + ω₃) :
    ω₁ * (rate * collisionFlux n₁ n₂ n₃) +
        ω₂ * (-(rate * collisionFlux n₁ n₂ n₃)) +
        ω₃ * (-(rate * collisionFlux n₁ n₂ n₃)) = 0 := by
  rw [hω]
  ring

/-- Entropy production is a nonnegative weight times a square. -/
theorem entropyProduction_eq_weighted_square
    {rate n₁ n₂ n₃ : Real}
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hn₃ : n₃ ≠ 0) :
    entropyProduction rate n₁ n₂ n₃ =
      rate * (n₁ * n₂ * n₃) * (inverseActionMismatch n₁ n₂ n₃) ^ 2 := by
  unfold entropyProduction
  rw [collisionFlux_factorization hn₁ hn₂ hn₃]
  ring

/-- A nonnegative collision rate and positive actions give nonnegative
logarithmic entropy production. -/
theorem entropyProduction_nonneg
    {rate n₁ n₂ n₃ : Real}
    (hrate : 0 ≤ rate) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) :
    0 ≤ entropyProduction rate n₁ n₂ n₃ := by
  rw [entropyProduction_eq_weighted_square
    (ne_of_gt hn₁) (ne_of_gt hn₂) (ne_of_gt hn₃)]
  positivity

/-- For positive actions, a zero collision flux is exactly inverse-action
balance. -/
theorem collisionFlux_eq_zero_iff_inverseActionMismatch_eq_zero
    {n₁ n₂ n₃ : Real} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) :
    collisionFlux n₁ n₂ n₃ = 0 ↔
      inverseActionMismatch n₁ n₂ n₃ = 0 := by
  rw [collisionFlux_factorization
    (ne_of_gt hn₁) (ne_of_gt hn₂) (ne_of_gt hn₃)]
  have hproduct : n₁ * n₂ * n₃ ≠ 0 := by
    positivity
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hproduct
  · intro h
    simp [h]

/-- Inverse-action balance in subtraction form is equivalent to the familiar
reciprocal collision-invariant equation. -/
theorem inverseActionMismatch_eq_zero_iff
    (n₁ n₂ n₃ : Real) :
    inverseActionMismatch n₁ n₂ n₃ = 0 ↔
      n₁⁻¹ = n₂⁻¹ + n₃⁻¹ := by
  unfold inverseActionMismatch
  constructor <;> intro h <;> linarith

/-- With strictly positive rate and actions, entropy production vanishes
exactly at inverse-action balance. -/
theorem entropyProduction_eq_zero_iff_inverseActionMismatch_eq_zero
    {rate n₁ n₂ n₃ : Real}
    (hrate : 0 < rate) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) :
    entropyProduction rate n₁ n₂ n₃ = 0 ↔
      inverseActionMismatch n₁ n₂ n₃ = 0 := by
  rw [entropyProduction_eq_weighted_square
    (ne_of_gt hn₁) (ne_of_gt hn₂) (ne_of_gt hn₃)]
  have hweight : rate * (n₁ * n₂ * n₃) ≠ 0 := by
    positivity
  constructor
  · intro h
    have hsquare := (mul_eq_zero.mp h).resolve_left hweight
    exact sq_eq_zero_iff.mp hsquare
  · intro h
    simp [h]

/-- Pointwise energy conservation for differentiable actions satisfying the
one-triad collision ODE.  This is an exact finite-dimensional chain-rule
statement, not a derivation of that ODE from a lattice. -/
theorem hasDerivAt_triadEnergy_of_collisionRates
    (n₁ n₂ n₃ : Real → Real) (t rate ω₁ ω₂ ω₃ : Real)
    (hω : ω₁ = ω₂ + ω₃)
    (h₁ : HasDerivAt n₁
      (rate * collisionFlux (n₁ t) (n₂ t) (n₃ t)) t)
    (h₂ : HasDerivAt n₂
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t)
    (h₃ : HasDerivAt n₃
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t) :
    HasDerivAt
      (fun s => triadEnergy ω₁ ω₂ ω₃ (n₁ s) (n₂ s) (n₃ s)) 0 t := by
  have hslope := weightedEnergySlope_eq_zero_of_resonance
    ω₁ ω₂ ω₃ rate (n₁ t) (n₂ t) (n₃ t) hω
  have hderiv :=
    ((HasDerivAt.const_mul ω₁ h₁).add (HasDerivAt.const_mul ω₂ h₂)).add
      (HasDerivAt.const_mul ω₃ h₃)
  change HasDerivAt
    (((fun s => ω₁ * n₁ s) + fun s => ω₂ * n₂ s) + fun s => ω₃ * n₃ s) 0 t
  rw [← hslope]
  exact hderiv

/-- Pointwise logarithmic-entropy chain rule for the one-triad collision ODE. -/
theorem hasDerivAt_triadLogEntropy_of_collisionRates
    (n₁ n₂ n₃ : Real → Real) (t rate : Real)
    (h₁ : HasDerivAt n₁
      (rate * collisionFlux (n₁ t) (n₂ t) (n₃ t)) t)
    (h₂ : HasDerivAt n₂
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t)
    (h₃ : HasDerivAt n₃
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t)
    (hn₁ : 0 < n₁ t) (hn₂ : 0 < n₂ t) (hn₃ : 0 < n₃ t) :
    HasDerivAt
      (fun s => triadLogEntropy (n₁ s) (n₂ s) (n₃ s))
      (entropyProduction rate (n₁ t) (n₂ t) (n₃ t)) t := by
  have hderivative :
      rate * collisionFlux (n₁ t) (n₂ t) (n₃ t) / n₁ t +
          (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) / n₂ t +
          (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) / n₃ t =
        entropyProduction rate (n₁ t) (n₂ t) (n₃ t) := by
    unfold entropyProduction inverseActionMismatch
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hlog := ((h₁.log (ne_of_gt hn₁)).add (h₂.log (ne_of_gt hn₂))).add
    (h₃.log (ne_of_gt hn₃))
  rw [hderivative] at hlog
  change HasDerivAt
    (((fun s => Real.log (n₁ s)) + fun s => Real.log (n₂ s)) +
      fun s => Real.log (n₃ s))
    (entropyProduction rate (n₁ t) (n₂ t) (n₃ t)) t
  exact hlog

/-- Along the one-triad ODE, a nonnegative rate makes the pointwise derivative
of logarithmic entropy nonnegative. -/
theorem triadLogEntropy_derivative_nonneg_of_collisionRates
    (n₁ n₂ n₃ : Real → Real) (t rate : Real)
    (hrate : 0 ≤ rate)
    (h₁ : HasDerivAt n₁
      (rate * collisionFlux (n₁ t) (n₂ t) (n₃ t)) t)
    (h₂ : HasDerivAt n₂
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t)
    (h₃ : HasDerivAt n₃
      (-(rate * collisionFlux (n₁ t) (n₂ t) (n₃ t))) t)
    (hn₁ : 0 < n₁ t) (hn₂ : 0 < n₂ t) (hn₃ : 0 < n₃ t) :
    HasDerivAt
        (fun s => triadLogEntropy (n₁ s) (n₂ s) (n₃ s))
        (entropyProduction rate (n₁ t) (n₂ t) (n₃ t)) t ∧
      0 ≤ entropyProduction rate (n₁ t) (n₂ t) (n₃ t) := by
  exact ⟨hasDerivAt_triadLogEntropy_of_collisionRates
      n₁ n₂ n₃ t rate h₁ h₂ h₃ hn₁ hn₂ hn₃,
    entropyProduction_nonneg hrate hn₁ hn₂ hn₃⟩

end

end ArchonPhysics.ThreeWaveCollisionAlgebra

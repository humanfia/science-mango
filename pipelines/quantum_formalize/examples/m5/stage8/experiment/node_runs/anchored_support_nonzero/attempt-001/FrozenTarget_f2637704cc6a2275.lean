import M5PackingInjective
import M5SupportPolynomial

theorem M5.SupportPolynomial.support_coeff_zero : ∀ S : Finset ℕ, (M5.SupportPolynomial.ofSupport S).coeff 0 = if 0 ∈ S then 1 else 0 := by
  classical
  intro S
  simp [M5.SupportPolynomial.ofSupport, Polynomial.coeff_X_pow]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ S : Finset ℕ, 0 ∈ S → M5.SupportPolynomial.ofSupport S ≠ 0

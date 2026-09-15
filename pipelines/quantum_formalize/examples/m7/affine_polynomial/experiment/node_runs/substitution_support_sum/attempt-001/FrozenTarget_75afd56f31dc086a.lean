import M7AffinePolynomial

theorem M7.AffinePolynomial.support_sum : ∀ (N : ℕ) [NeZero N], ∀ A : M7.Supports.Support N, M7.AffinePolynomial.image A = ∑ i ∈ A, M7.CyclicSubstitution.rho N ^ i.val := by
  intro N inst A
  classical
  simp [M7.AffinePolynomial.image, M7.Supports.polynomial,
    M6.Cyclic.image, M7.CyclicSubstitution.rho, map_sum,
    map_pow, AdjoinRoot.mk_X]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (A : M7.Supports.Support N), M7.QuotientAuto.substitution u (M7.AffinePolynomial.image A) = ∑ i ∈ A, M7.CyclicSubstitution.point u ^ i.val

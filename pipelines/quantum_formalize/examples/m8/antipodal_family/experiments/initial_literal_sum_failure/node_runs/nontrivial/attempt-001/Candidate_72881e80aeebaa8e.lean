import FrozenTarget_72881e80aeebaa8e
theorem M8.AntipodalFamily.nontrivial : QuantumHarnessFrozenTarget := by
  intro N inst hN hEven
  have hhalf : 0 < N / 2 := by omega
  have monic_binomial : ∀ (R : Type) [CommRing R] (k : ℕ), 0 < k → (1 + (Polynomial.X : Polynomial R) ^ k).Monic := by
    intro R _ k hk
    first
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) (ne_of_gt hk) 1)
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) 1 (ne_of_gt hk))
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) hk 1)
    | simpa only [Polynomial.C_1, add_comm] using (Polynomial.monic_X_pow_add_C (R := R) 1 hk)
  have h₁ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial)).Monic := by
    simpa using monic_binomial _ 1 (by omega)
  have h₂ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (N / 2)).Monic :=
    monic_binomial _ _ hhalf
  have hm : (M8.AntipodalFamily.polynomial N).Monic := by
    exact h₁.mul h₂
  have hd₁ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial)).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have hd₂ : (1 + (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (N / 2)).natDegree = N / 2 := by
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simpa using hhalf)]
    simp
  have hd : (M8.AntipodalFamily.polynomial N).natDegree = N / 2 + 1 := by
    unfold M8.AntipodalFamily.polynomial
    rw [Polynomial.natDegree_mul h₁.ne_zero h₂.ne_zero, hd₁, hd₂]
    omega
  refine ⟨hm, ?_, hm.ne_zero, hd⟩
  intro heq
  rw [heq, Polynomial.natDegree_one] at hd
  omega

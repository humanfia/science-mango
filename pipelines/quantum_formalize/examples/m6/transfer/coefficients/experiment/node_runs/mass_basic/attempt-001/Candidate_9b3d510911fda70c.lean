import FrozenTarget_9b3d510911fda70c
theorem M6.Transfer.mass_basic : QuantumHarnessFrozenTarget := by
  classical
  change M6.Transfer.polynomialMass (0 : Polynomial ℤ) = 0 ∧ M6.Transfer.polynomialMass (1 : Polynomial ℤ) = 1 ∧ (∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs) ∧ ∀ (p : Polynomial ℤ) (d : ℕ), (p.coeff d).natAbs ≤ M6.Transfer.polynomialMass p
  have hm : ∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs := by
    intro n c
    simp [M6.Transfer.polynomialMass, Polynomial.sum_monomial_index]
  refine ⟨?_, ?_, hm, ?_⟩
  · simp [M6.Transfer.polynomialMass]
  · simpa using hm 0 1
  · intro p d
    by_cases h : p.coeff d = 0
    · simp [h]
    · unfold M6.Transfer.polynomialMass
      rw [Polynomial.sum_eq_of_subset _ (by intro i; rfl) (by intro i hi; exact hi : p.support ⊆ p.support)]
      exact Finset.single_le_sum (fun i hi => Nat.zero_le _) (Polynomial.mem_support_iff.mpr h)

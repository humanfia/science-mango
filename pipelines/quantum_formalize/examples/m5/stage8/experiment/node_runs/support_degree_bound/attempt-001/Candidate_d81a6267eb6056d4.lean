import FrozenTarget_d81a6267eb6056d4
theorem M5.SupportPolynomial.support_degree_bound : QuantumHarnessFrozenTarget := by
  change ∀ (S : Finset ℕ) (K : ℕ), 0 < K → (∀ e ∈ S, e < K) → (M5.SupportPolynomial.ofSupport S).natDegree < K
  intro S K hK
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      simpa [M5.SupportPolynomial.ofSupport] using hK
  | @insert a S ha ih =>
      intro hS
      rw [M5.SupportPolynomial.ofSupport, Finset.sum_insert ha]
      apply lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      apply max_lt_iff.mpr
      constructor
      · simpa only [Polynomial.natDegree_X_pow] using hS a (Finset.mem_insert_self a S)
      · simpa only [M5.SupportPolynomial.ofSupport] using
          ih (fun e he => hS e (Finset.mem_insert_of_mem he))

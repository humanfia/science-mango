import FrozenTarget_81b7ee1ffd663e06
theorem M5.RepairSupport.replacement_polynomial_residue : QuantumHarnessFrozenTarget := by
  intro A e k T he hf
  classical
  have hf' : e + k * T ∉ A.erase e := by
    intro h
    exact hf (Finset.mem_of_mem_erase h)
  unfold M5.RepairSupport.repaired M5.SupportPolynomial.ofSupport
  rw [Finset.sum_insert hf']
  conv_rhs =>
    rw [← Finset.insert_erase he, Finset.sum_insert (Finset.notMem_erase e A)]
  rw [map_add, map_add]
  congr 1
  first
  | apply M5.quotient_monomial_period
  | apply M5.SupportPolynomial.quotient_monomial_period
  | simpa only [Polynomial.monomial_one] using
      (M5.quotient_monomial_period (T := T) (a := e) (j := k))

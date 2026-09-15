import FrozenTarget_c0e9eb56b70ee465
theorem M5.ResidueNecessity.reduced_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro w T hT u hu
  change AdjoinRoot.mk (M5.cyclicModulus T)
      (∑ a ∈ Finset.univ.image u, (Polynomial.X : M5.BinaryPolynomial) ^ a) =
    AdjoinRoot.mk (M5.cyclicModulus T)
      (∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ (u i % T))
  rw [Finset.sum_image (fun i _ j _ hij => hu hij)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : u i % T + (u i / T) * T = u i := by
    rw [Nat.mul_comm (u i / T) T]
    exact Nat.mod_add_div (u i) T
  have hp := M5.SupportPolynomial.quotient_monomial_period T (u i % T) (u i / T)
  rw [he] at hp
  exact hp

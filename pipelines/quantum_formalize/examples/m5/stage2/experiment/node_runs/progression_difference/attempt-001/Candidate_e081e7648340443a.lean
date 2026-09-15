import FrozenTarget_e081e7648340443a
theorem M5.Lift.progression_difference : QuantumHarnessFrozenTarget := by
  change ∀ T E j : ℕ, M5.cyclicModulus (T + j * E) - M5.cyclicModulus T = (Polynomial.X : M5.BinaryPolynomial) ^ T * M5.cyclicModulus (j * E)
  intro T E j
  simp only [M5.Lift.cyclic_as_sub, pow_add]
  ring

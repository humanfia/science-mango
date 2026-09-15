import FrozenTarget_02562c412576c3f2
theorem M5.Character.character_add : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (λ z u : M5.Character.BinaryVector D), M5.Character.value λ (z + u) = M5.Character.value λ z * M5.Character.value λ u
  intro D λ z u
  simp only [M5.Character.value, Pi.add_apply, M5.Character.bit_add, Finset.prod_mul_distrib]

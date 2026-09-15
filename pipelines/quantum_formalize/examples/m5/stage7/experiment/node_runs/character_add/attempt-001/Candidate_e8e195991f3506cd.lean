import FrozenTarget_e8e195991f3506cd
theorem M5.Character.character_add : QuantumHarnessFrozenTarget := by
  change ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u
  intro D lam z u
  simp only [M5.Character.value, Pi.add_apply, M5.Character.bit_add, Finset.prod_mul_distrib]

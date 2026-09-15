import FrozenTarget_eddc57c9ff6ac85e
theorem M6.Character.character_add : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (q r z : M6.Character.Vector m), M6.Character.character (q + r) z = M6.Character.character q z * M6.Character.character r z
  intro m q r z
  simp only [M6.Character.character, M6.Character.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib, M6.Character.sign_add]

import FrozenTarget_d9357e9b60dbda8b
theorem M6.Character.character_product : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (q z : M6.Character.Vector m), M6.Character.character q z = ∏ i, M6.Character.sign (q i * z i)
  intro m q z
  change M6.Character.sign (∑ i, q i * z i) = ∏ i, M6.Character.sign (q i * z i)
  exact M6.Character.sign_sum m (fun i => q i * z i)

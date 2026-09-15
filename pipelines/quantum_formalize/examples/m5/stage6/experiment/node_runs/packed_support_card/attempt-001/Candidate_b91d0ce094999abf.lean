import FrozenTarget_b91d0ce094999abf
theorem M5.Packing.packed_support_card : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w
  intro w T r
  classical
  unfold M5.Packing.packedSupport
  rw [Finset.card_image_of_injective _ (M5.Packing.packed_value_injective w T r)]
  simp

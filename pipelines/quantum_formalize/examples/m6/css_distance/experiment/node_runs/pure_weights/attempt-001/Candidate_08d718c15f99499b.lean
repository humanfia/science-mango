import FrozenTarget_08d718c15f99499b
theorem M6.CSS.pure_weights : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v
  intro m v
  classical
  simp [M6.CSS.weight, M6.CSS.support, M6.Pinned.weight]

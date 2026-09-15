import FrozenTarget_0b79547d4d8a8210
theorem M6.Flatten.flatten_smul : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z
  intro N c z
  funext i
  simp only [M6.Flatten.flatten, Pi.smul_apply]
  split <;> simp_all

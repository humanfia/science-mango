import FrozenTarget_575147210bee9c3d
theorem M7.CanonicalBlock.key_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalBlock.key (N := N))
  intro N inst A B h
  have hd := congrArg (M7.CanonicalBlock.decode N) h
  rw [M7.CanonicalBlock.decode_key N A, M7.CanonicalBlock.decode_key N B] at hd
  exact hd

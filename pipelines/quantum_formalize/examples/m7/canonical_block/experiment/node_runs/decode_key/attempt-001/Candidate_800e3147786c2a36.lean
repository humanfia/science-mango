import FrozenTarget_800e3147786c2a36
theorem M7.CanonicalBlock.decode_key : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.decode N (M7.CanonicalBlock.key A) = A
  intro N inst A
  classical
  simp [M7.CanonicalBlock.decode, M7.CanonicalBlock.key, Finset.image_image]

import M7CanonicalBlock

theorem M7.CanonicalBlock.decode_key : ∀ (N : ℕ) [NeZero N], ∀ A : M7.CanonicalBlock.Support N, M7.CanonicalBlock.decode N (M7.CanonicalBlock.key A) = A := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.CanonicalBlock.Support N), M7.CanonicalBlock.decode N (M7.CanonicalBlock.key A) = A
  intro N inst A
  classical
  simp [M7.CanonicalBlock.decode, M7.CanonicalBlock.key, Finset.image_image]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], Function.Injective (M7.CanonicalBlock.key (N := N))

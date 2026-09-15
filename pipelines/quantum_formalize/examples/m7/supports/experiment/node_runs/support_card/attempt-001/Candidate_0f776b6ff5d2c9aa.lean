import FrozenTarget_0f776b6ff5d2c9aa
theorem M7.Supports.support_card : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support.card = A.card
  intro N inst A
  rw [M7.Supports.support N A]
  unfold M7.Supports.natSupport
  exact Finset.card_image_of_injective A (ZMod.val_injective N)

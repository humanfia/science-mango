import FrozenTarget_c8e2cab10805fb63
theorem M7.CanonicalBlock.normalize_card : QuantumHarnessFrozenTarget := by
  intro N inst A
  change (M7.CanonicalBlock.shift (-M7.CanonicalBlock.bestAnchor A) A).card = A.card
  exact M7.CanonicalBlock.shift_card N (-M7.CanonicalBlock.bestAnchor A) A

import FrozenTarget_ad44b46a22f53f1b
theorem M6.Transfer.labels_bijective : QuantumHarnessFrozenTarget := by
  change ∀ (R N : ℕ) [NeZero N], Function.Bijective (M6.Transfer.labels : M6.Transfer.ClosedWalk R N → M6.Transfer.Input N)
  intro R N inst
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      rw [M6.Transfer.memory_forced R N p i j,
        M6.Transfer.memory_forced R N q i j, hpq]
    · exact hpq
  · intro h
    exact ⟨⟨(M6.Transfer.memoryAt h, h), M6.Transfer.memory_follows R N h⟩, rfl⟩

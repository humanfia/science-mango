import FrozenTarget_54f875fc2a288a95
theorem M6.Transfer.closed_walk_card : QuantumHarnessFrozenTarget := by
  change ∀ (R N : ℕ) [NeZero N], Fintype.card (M6.Transfer.ClosedWalk R N) = 2 ^ N
  intro R N inst
  classical
  calc
    Fintype.card (M6.Transfer.ClosedWalk R N) = Fintype.card (M6.Transfer.Input N) :=
      Fintype.card_congr (Equiv.ofBijective M6.Transfer.labels (M6.Transfer.labels_bijective R N))
    _ = 2 ^ N := by
      simp [M6.Transfer.Input, M6.Transfer.Bit, Fintype.card_fun, ZMod.card]

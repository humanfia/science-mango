import FrozenTarget_fa6d6b11ac1d6a5b
theorem M6.Pinned.weight_bound : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m
  intro m v
  classical
  unfold M6.Pinned.weight
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

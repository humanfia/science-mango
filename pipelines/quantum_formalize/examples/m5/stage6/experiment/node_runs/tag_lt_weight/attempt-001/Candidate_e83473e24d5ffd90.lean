import FrozenTarget_e83473e24d5ffd90
theorem M5.Packing.tag_lt_weight : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w
  intro w T r i
  classical
  unfold M5.Packing.occurrenceTag
  have hw : (Finset.univ : Finset (Fin w)).card = w := by simp
  rw [← hw]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hi := Finset.mem_univ i
  rw [← h] at hi
  simpa using hi

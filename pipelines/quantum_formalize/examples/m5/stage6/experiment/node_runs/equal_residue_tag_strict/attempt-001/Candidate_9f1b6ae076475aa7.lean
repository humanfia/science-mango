import FrozenTarget_9f1b6ae076475aa7
theorem M5.Packing.equal_residue_tag_strict : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i j : Fin w), i < j → r i = r j → M5.Packing.occurrenceTag r i < M5.Packing.occurrenceTag r j
  intro w T r i j hij hr
  classical
  change (M5.Packing.priorOccurrences r i).card < (M5.Packing.priorOccurrences r j).card
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [M5.Packing.priorOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨lt_trans hk.1 hij, hk.2.trans hr⟩
  · intro heq
    have hi : i ∈ M5.Packing.priorOccurrences r j := by
      simpa [M5.Packing.priorOccurrences] using And.intro hij hr
    rw [← heq] at hi
    simpa [M5.Packing.priorOccurrences] using hi

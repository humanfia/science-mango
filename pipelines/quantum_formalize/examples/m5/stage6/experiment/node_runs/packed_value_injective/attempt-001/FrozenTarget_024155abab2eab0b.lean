import M5Packing

theorem M5.Packing.equal_residue_tag_strict : ∀ (w T : ℕ) (r : Fin w → Fin T) (i j : Fin w), i < j → r i = r j → M5.Packing.occurrenceTag r i < M5.Packing.occurrenceTag r j := by
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

theorem M5.Packing.packed_value_mod : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val
  intro w T r i
  simp [M5.Packing.packedValue, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (r i).isLt]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r)

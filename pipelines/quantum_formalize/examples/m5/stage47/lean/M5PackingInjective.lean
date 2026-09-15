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

theorem M5.Packing.packed_value_injective : ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r)
  intro w T r i j h
  have hrval : (r i).val = (r j).val := by
    have hm := congrArg (fun n : ℕ => n % T) h
    simpa only [M5.Packing.packed_value_mod] using hm
  have hr : r i = r j := Fin.ext hrval
  have hT : 0 < T := lt_of_le_of_lt (Nat.zero_le _) (r i).isLt
  have hmul : T * M5.Packing.occurrenceTag r i = T * M5.Packing.occurrenceTag r j := by
    unfold M5.Packing.packedValue at h
    nlinarith [hrval]
  have htag : M5.Packing.occurrenceTag r i = M5.Packing.occurrenceTag r j :=
    Nat.eq_of_mul_eq_mul_left hT hmul
  rcases lt_trichotomy i j with hij | hij | hji
  · have hs := M5.Packing.equal_residue_tag_strict w T r i j hij hr
    omega
  · exact hij
  · have hs := M5.Packing.equal_residue_tag_strict w T r j i hji hr.symm
    omega

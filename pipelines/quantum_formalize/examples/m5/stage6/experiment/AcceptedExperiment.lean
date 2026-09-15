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

theorem M5.Packing.packed_support_anchor : ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (hw : 0 < w), (r ⟨0, hw⟩).val = 0 → 0 ∈ M5.Packing.packedSupport r
  intro w T r hw h
  unfold M5.Packing.packedSupport
  apply Finset.mem_image.mpr
  refine ⟨⟨0, hw⟩, Finset.mem_univ _, ?_⟩
  simp [M5.Packing.packedValue, M5.Packing.occurrenceTag, M5.Packing.priorOccurrences, Fin.lt_def, h]

theorem M5.Packing.packed_value_mod : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.packedValue r i % T = (r i).val
  intro w T r i
  simp [M5.Packing.packedValue, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (r i).isLt]

theorem M5.Packing.tag_lt_weight : ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (i : Fin w), M5.Packing.occurrenceTag r i < w
  intro w T r i
  classical
  unfold M5.Packing.occurrenceTag
  have hs : M5.Packing.priorOccurrences r i ⊂ (Finset.univ : Finset (Fin w)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    have hi : i ∈ M5.Packing.priorOccurrences r i := by
      rw [h]
      exact Finset.mem_univ i
    simpa [M5.Packing.priorOccurrences] using hi
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hs

theorem M5.Packing.packed_support_range : ∀ (w T : ℕ) (r : Fin w → Fin T) (e : ℕ), e ∈ M5.Packing.packedSupport r → e < w * T := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T) (e : ℕ), e ∈ M5.Packing.packedSupport r → e < w * T
  intro w T r e he
  classical
  unfold M5.Packing.packedSupport at he
  rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
  change (r i).val + M5.Packing.occurrenceTag r i * T < w * T
  have hr := (r i).isLt
  have ht := M5.Packing.tag_lt_weight w T r i
  have hm := Nat.mul_le_mul_right T (Nat.succ_le_of_lt ht)
  nlinarith

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

theorem M5.Packing.packed_support_card : ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w := by
  change ∀ (w T : ℕ) (r : Fin w → Fin T), (M5.Packing.packedSupport r).card = w
  intro w T r
  classical
  unfold M5.Packing.packedSupport
  rw [Finset.card_image_of_injective _ (M5.Packing.packed_value_injective w T r)]
  simp
#print axioms M5.Packing.equal_residue_tag_strict
#print axioms M5.Packing.packed_support_anchor
#print axioms M5.Packing.packed_value_mod
#print axioms M5.Packing.packed_value_injective
#print axioms M5.Packing.packed_support_card
#print axioms M5.Packing.tag_lt_weight
#print axioms M5.Packing.packed_support_range

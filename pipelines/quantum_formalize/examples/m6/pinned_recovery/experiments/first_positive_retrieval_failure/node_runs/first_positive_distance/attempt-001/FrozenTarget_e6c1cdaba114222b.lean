import M6Pinned

theorem M6.Pinned.count_nonnegative_positive : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), 0 ≤ M6.Pinned.count L P d ∧ (0 < M6.Pinned.count L P d ↔ ∃ v ∈ L, M6.Pinned.agrees P v ∧ M6.Pinned.weight v = d) := by
  classical
  intro m L P d
  unfold M6.Pinned.count
  constructor
  · exact Int.natCast_nonneg _
  · simp [Int.natCast_pos, Finset.card_pos, Finset.Nonempty, and_assoc]

theorem M6.Pinned.distance_spec : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), (M6.Pinned.distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, (M6.Pinned.distance L = some d ↔ (∃ v ∈ L, M6.Pinned.weight v = d) ∧ ∀ v ∈ L, d ≤ M6.Pinned.weight v) := by
  classical
  intro m L
  by_cases h : L.Nonempty
  · have hi : (L.image M6.Pinned.weight).Nonempty := h.image M6.Pinned.weight
    constructor
    · simp [M6.Pinned.distance, h, h.ne_empty]
    · intro d
      change (if h : L.Nonempty then
        some ((L.image M6.Pinned.weight).min' (h.image M6.Pinned.weight))
        else none) = some d ↔ _
      rw [dif_pos h, Option.some.injEq]
      constructor
      · intro hd
        obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp
          (Finset.min'_mem (L.image M6.Pinned.weight) hi)
        constructor
        · exact ⟨v, hv, hw.trans hd⟩
        · intro w hw
          rw [← hd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
      · rintro ⟨⟨v, hv, hvd⟩, hleast⟩
        apply le_antisymm
        · rw [← hvd]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · obtain ⟨w, hw, hweight⟩ := Finset.mem_image.mp
            (Finset.min'_mem (L.image M6.Pinned.weight) hi)
          rw [← hweight]
          exact hleast w hw
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst L
    simp [M6.Pinned.distance]

theorem M6.Pinned.enumerator_coeff : ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d
  intro m L P d
  classical
  simp only [M6.Pinned.enumerator, M6.Pinned.count,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hrev : (d = M6.Pinned.weight v) ↔ (M6.Pinned.weight v = d) := eq_comm
  by_cases ha : M6.Pinned.agrees P v <;>
    by_cases hw : M6.Pinned.weight v = d <;>
    simp [ha, hw, Polynomial.coeff_X_pow, eq_comm]
  all_goals omega

theorem M6.Pinned.weight_bound : ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m := by
  change ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m
  intro m v
  classical
  unfold M6.Pinned.weight
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), M6.Pinned.firstPositive m (M6.Pinned.enumerator L (M6.Pinned.free m)) = M6.Pinned.distance L

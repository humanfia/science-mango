import FrozenTarget_716cf87c67af4892
theorem M6.Pinned.distance_spec : QuantumHarnessFrozenTarget := by
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

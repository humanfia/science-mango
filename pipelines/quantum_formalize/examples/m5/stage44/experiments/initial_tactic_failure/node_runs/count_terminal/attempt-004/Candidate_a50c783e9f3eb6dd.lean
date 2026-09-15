import FrozenTarget_a50c783e9f3eb6dd
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
  intro α _ W m p hW hp
  classical
  have hprefix : ∀ q ∈ W, p <+: q ↔ q = p := by
    intro q hq
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · intro h
      subst q
      exact ⟨[], by simp⟩
  change ((W.filter (fun q => p <+: q)).card : ℤ) = (if p ∈ W then 1 else 0)
  by_cases hmem : p ∈ W
  · have hf : W.filter (fun q => p <+: q) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact (hprefix q h.1).mp h.2
      · intro h
        subst q
        exact ⟨hmem, ⟨[], by simp⟩⟩
    rw [hf]
    simp [hmem]
  · have hf : W.filter (fun q => p <+: q) = ∅ := by
      ext q
      constructor
      · intro h
        obtain ⟨hq, hpq⟩ := Finset.mem_filter.mp h
        have he : q = p := (hprefix q hq).mp hpq
        subst q
        exact (hmem hq).elim
      · intro h
        simp at h
    rw [hf]
    simp [hmem]

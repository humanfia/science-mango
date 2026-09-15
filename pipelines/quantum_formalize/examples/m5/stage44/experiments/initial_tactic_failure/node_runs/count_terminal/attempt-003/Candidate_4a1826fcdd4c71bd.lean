import FrozenTarget_4a1826fcdd4c71bd
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
  intro α _ W m p hW hp
  classical
  have hprefix : ∀ q ∈ W, p <+: q ↔ q = p := by
    intro q hq
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · rintro rfl
      exact List.IsPrefix.refl p
  have hf : W.filter (fun q => p = q) =
      (if p ∈ W then {p} else ∅) := by
    ext q
    by_cases hmem : p ∈ W
    · simp only [hmem, if_pos, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact h.2.symm
      · intro h
        subst q
        exact ⟨hmem, rfl⟩
    · simp only [hmem, if_neg, Finset.mem_filter, Finset.not_mem_empty, iff_false]
      rintro ⟨hq, rfl⟩
      exact hmem hq
  simp +contextual [M5.PrefixPartition.count, hprefix, eq_comm]
  rw [hf]
  by_cases hmem : p ∈ W <;> simp [hmem]

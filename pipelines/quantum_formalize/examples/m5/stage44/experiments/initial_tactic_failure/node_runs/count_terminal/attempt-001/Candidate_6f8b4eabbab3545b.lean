import FrozenTarget_6f8b4eabbab3545b
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
    classical
    intro α _ W m p hW hp
    change ((W.filter (fun q => p <+: q)).card : ℤ) = (if p ∈ W then 1 else 0)
    have heq : ∀ q ∈ W, (p <+: q) ↔ q = p := by
      intro q hq
      constructor
      · intro h
        exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
      · intro h
        subst q
        exact List.IsPrefix.refl _
    by_cases hmem : p ∈ W
    · have hf : W.filter (fun q => p <+: q) = {p} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hq, hprefix⟩
          exact (heq q hq).mp hprefix
        · intro h
          subst q
          exact ⟨hmem, List.IsPrefix.refl _⟩
      simp [hf, hmem]
    · have hf : W.filter (fun q => p <+: q) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        obtain ⟨hqW, hprefix⟩ := Finset.mem_filter.mp hq
        have hqp := (heq q hqW).mp hprefix
        subst q
        exact hmem hqW
      simp [hf, hmem]

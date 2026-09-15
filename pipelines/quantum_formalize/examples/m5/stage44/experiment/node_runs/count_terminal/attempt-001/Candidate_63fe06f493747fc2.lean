import FrozenTarget_63fe06f493747fc2
theorem M5.PrefixPartition.count_terminal : QuantumHarnessFrozenTarget := by
  intro α inst W m p hW hp
  classical
  have hcount : M5.PrefixPartition.count W p = ((W.filter (fun q => p.IsPrefix q)).card : ℤ) := by
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List α) => (s.card : ℤ))
    ext q
    simp only [Finset.mem_filter]
  have hf : W.filter (fun q => p.IsPrefix q) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · intro h
      subst q
      exact List.prefix_refl p
  rw [hcount, hf]
  by_cases h : p ∈ W
  · have hs : W.filter (fun q => q = p) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hq => hq.2
      · intro hq
        subst q
        exact ⟨h, rfl⟩
    rw [hs]
    simp [h]
  · simp [h]

import FrozenTarget_a1ae8f3e9aad30b0
theorem M8.OrbitSpan.small_iff : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c hc₁ hc₂ L
  have hn := M8.OrbitSpan.spans_nonempty N c hc₁ hc₂
  rw [M8.OrbitSpan.value, dif_pos hn]
  constructor
  · intro h
    have hm := Finset.min'_mem (M8.OrbitSpan.spans c) hn
    unfold M8.OrbitSpan.spans at hm
    rcases Finset.mem_image.mp hm with ⟨g, hg, heq⟩
    exact ⟨g, (Finset.mem_filter.mp hg).2, heq.trans_le h⟩
  · rintro ⟨g, hg, hL⟩
    have hm : M8.Anchor.span (M7.Action.act g c) ∈ M8.OrbitSpan.spans c := by
      unfold M8.OrbitSpan.spans
      exact Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩, rfl⟩
    exact le_trans (Finset.min'_le _ _ hm) hL

import FrozenTarget_14db3f321d527989
theorem M8.OrbitSpan.attained : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c hc₁ hc₂
  have hne := M8.OrbitSpan.spans_nonempty N c hc₁ hc₂
  have hm : M8.OrbitSpan.value c ∈ M8.OrbitSpan.spans c := by
    simpa [M8.OrbitSpan.value, hne] using Finset.min'_mem (M8.OrbitSpan.spans c) hne
  unfold M8.OrbitSpan.spans at hm
  rcases Finset.mem_image.mp hm with ⟨g, hg, heq⟩
  exact ⟨g, (Finset.mem_filter.mp hg).2, heq⟩

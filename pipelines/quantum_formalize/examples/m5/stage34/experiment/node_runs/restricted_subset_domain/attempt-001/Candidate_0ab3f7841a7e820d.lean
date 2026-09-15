import FrozenTarget_0ab3f7841a7e820d
theorem M5.ConditionalCount.restricted_subset_domain : QuantumHarnessFrozenTarget := by
  intro W d k
  classical
  change (W.filter (fun s => d ∣ s)).powersetCard k =
    (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  apply Finset.ext
  intro U
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hk⟩
    refine ⟨⟨?_, hk⟩, ?_⟩
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).1
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).2
  · rintro ⟨⟨hU, hk⟩, hd⟩
    refine ⟨?_, hk⟩
    intro s hs
    exact Finset.mem_filter.mpr ⟨hU hs, hd s hs⟩

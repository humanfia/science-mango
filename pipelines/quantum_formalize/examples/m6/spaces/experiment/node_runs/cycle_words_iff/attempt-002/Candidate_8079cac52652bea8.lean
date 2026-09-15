import FrozenTarget_8079cac52652bea8
theorem M6.Spaces.cycle_words_iff : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b v
  classical
  change v ∈ Finset.filter (M6.Character.Orthogonal (M6.Spaces.dualBoundary N a b).range) Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (∀ q, q ∈ (M6.Spaces.dualBoundary N a b).range → M6.Character.dot q v = 0) ↔ _
  rw [M6.Flatten.cycle_orthogonal]
  constructor
  · intro hv h
    exact hv _ ⟨h, rfl⟩
  · intro hv q hq
    obtain ⟨h, rfl⟩ := hq
    exact hv h

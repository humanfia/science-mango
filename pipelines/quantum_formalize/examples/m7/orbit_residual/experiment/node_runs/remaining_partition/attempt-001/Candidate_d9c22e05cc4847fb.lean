import FrozenTarget_d9c22e05cc4847fb
theorem M7.OrbitResidual.remaining_partition : QuantumHarnessFrozenTarget := by
  classical
  intro N inst C0 C1 bases
  unfold M7.OrbitResidual.remaining
  apply Finset.ext
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h0 | h1, h⟩
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h1, h⟩
  · rintro (⟨h0, h⟩ | ⟨h1, h⟩)
    · exact ⟨Or.inl h0, h⟩
    · exact ⟨Or.inr h1, h⟩

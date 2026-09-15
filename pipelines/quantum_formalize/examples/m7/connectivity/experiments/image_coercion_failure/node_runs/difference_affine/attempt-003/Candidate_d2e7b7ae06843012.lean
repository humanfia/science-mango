import FrozenTarget_d2e7b7ae06843012
theorem M7.Connectivity.difference_affine : QuantumHarnessFrozenTarget := by
  intro N inst A u s
  classical
  apply Set.ext
  intro x
  simp only [M7.Connectivity.differences, Set.mem_setOf_eq, Set.mem_image,
    Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨a₀, ha₀, rfl⟩, b, ⟨b₀, hb₀, rfl⟩, hx⟩
    refine ⟨a₀ - b₀, ⟨a₀, ha₀, b₀, hb₀, rfl⟩, ?_⟩
    first
    | simpa [M7.Action.affine, mul_sub] using hx
    | simpa [M7.Action.affine, mul_sub] using hx.symm
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, hx⟩
    refine ⟨M7.Action.affine u s a, ⟨a, ha, rfl⟩,
      M7.Action.affine u s b, ⟨b, hb, rfl⟩, ?_⟩
    first
    | simpa [M7.Action.affine, mul_sub] using hx
    | simpa [M7.Action.affine, mul_sub] using hx.symm

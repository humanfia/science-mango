import FrozenTarget_3d6c9322e5661e13
theorem M7.Connectivity.difference_affine : QuantumHarnessFrozenTarget := by
  intro N _ A u s
  classical
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨a, ha, b, hb, h⟩
    rcases Finset.mem_image.mp ha with ⟨a₀, ha₀, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b₀, hb₀, rfl⟩
    subst x
    refine Set.mem_image.mpr ⟨a₀ - b₀, ⟨a₀, ha₀, b₀, hb₀, rfl⟩, ?_⟩
    simp [M7.Action.affine, mul_sub]
  · intro hx
    rcases Set.mem_image.mp hx with ⟨d, hd, rfl⟩
    rcases hd with ⟨a, ha, b, hb, h⟩
    subst d
    refine ⟨M7.Action.affine u s a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      M7.Action.affine u s b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    simp [M7.Action.affine, mul_sub]

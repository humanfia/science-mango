import FrozenTarget_f1f71014ec3155d6
theorem M7.Connectivity.difference_affine : QuantumHarnessFrozenTarget := by
  intro N _ A u s
  classical
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨b, hb, rfl⟩
    refine ⟨a - b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    dsimp [M7.Action.affine]
    ring
  · intro hx
    rcases hx with ⟨d, hd, rfl⟩
    rcases hd with ⟨a, ha, b, hb, rfl⟩
    refine ⟨M7.Action.affine u s a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      M7.Action.affine u s b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    dsimp [M7.Action.affine]
    ring

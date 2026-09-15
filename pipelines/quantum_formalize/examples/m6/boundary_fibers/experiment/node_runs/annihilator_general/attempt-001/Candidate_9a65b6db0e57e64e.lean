import FrozenTarget_9a65b6db0e57e64e
theorem M6.BoundaryFibers.annihilator_general : QuantumHarnessFrozenTarget := by
  intro F M hF hFM hM
  rcases hFM with ⟨K, rfl⟩
  have hK : K ≠ 0 := by
    intro hK
    apply hM
    simp [hK]
  simpa only [M6.KernelFibers.annihilator] using
    (M6.KernelFibers.annihilator_card F K hF hK)

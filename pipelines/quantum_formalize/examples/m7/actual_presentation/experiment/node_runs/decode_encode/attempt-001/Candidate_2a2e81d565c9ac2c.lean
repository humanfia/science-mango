import FrozenTarget_2a2e81d565c9ac2c
theorem M7.ActualPresentation.decode_encode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N), M7.ActualPresentation.decode (M7.ActualPresentation.encode g) = g
  intro N inst g
  rcases g with ⟨u, s, t, e⟩
  simp [M7.ActualPresentation.decode, M7.ActualPresentation.encode,
    M7.Presentation.mk, M7.Presentation.outer, M7.Presentation.left,
    M7.Presentation.right, ZMod.natCast_zmod_val]

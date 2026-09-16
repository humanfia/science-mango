import FrozenTarget_0410bd994a677ce4
theorem M8.CoverageFoundation.affine_full : QuantumHarnessFrozenTarget := by
  intro N inst A u s
  simpa [M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction,
    M7.Connectivity.connected, M7.Action.act] using
    (M7.Connectivity.connected_action N (⟨u, false, s, s⟩ : M7.Action.Record N) (A, A))

import FrozenTarget_4096a6e1d2a7af13
theorem M6.ActualResult.Q_total : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h
  rw [M6.ActualResult.Q_enumerator N a b h]
  exact M6.Pinned.enumerator_total _ _

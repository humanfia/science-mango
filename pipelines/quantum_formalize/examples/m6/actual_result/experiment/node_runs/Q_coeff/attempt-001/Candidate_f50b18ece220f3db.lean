import FrozenTarget_f50b18ece220f3db
theorem M6.ActualResult.Q_coeff : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst a b h P d
  rw [M6.ActualResult.Q_enumerator N a b h P, M6.Pinned.enumerator_coeff (2*N)]
  exact ⟨rfl, (M6.Pinned.count_nonnegative_positive (2*N) _ P d).1⟩

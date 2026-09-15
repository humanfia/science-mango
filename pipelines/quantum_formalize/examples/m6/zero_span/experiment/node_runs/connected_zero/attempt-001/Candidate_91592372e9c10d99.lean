import FrozenTarget_91592372e9c10d99
theorem M6.ZeroSpan.connected_zero : QuantumHarnessFrozenTarget := by
  intro N h
  rcases h with ⟨_, _, _, _, _, hg⟩
  have hs : (1 : M6.Final.BP).support = {0} := by
    change (Polynomial.C (1 : ZMod 2)).support = {0}
    exact Polynomial.support_C (one_ne_zero : (1 : ZMod 2) ≠ 0)
  simpa [hs] using hg

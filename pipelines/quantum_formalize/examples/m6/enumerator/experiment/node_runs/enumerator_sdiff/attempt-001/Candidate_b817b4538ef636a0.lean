import FrozenTarget_b817b4538ef636a0
theorem M6.Pinned.enumerator_sdiff : QuantumHarnessFrozenTarget := by
  intro m B C P hBC
  classical
  unfold M6.Pinned.enumerator
  apply eq_sub_iff_add_eq.mpr
  exact Finset.sum_sdiff hBC

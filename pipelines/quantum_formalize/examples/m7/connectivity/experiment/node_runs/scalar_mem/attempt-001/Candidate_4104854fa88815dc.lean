import FrozenTarget_4104854fa88815dc
theorem M7.Connectivity.scalar_mem : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r * a ∈ H
  intro N inst H a r ha
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using H.nsmul_mem ha r.val

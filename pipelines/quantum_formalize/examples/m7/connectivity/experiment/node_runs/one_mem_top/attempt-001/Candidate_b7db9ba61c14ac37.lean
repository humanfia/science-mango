import FrozenTarget_b7db9ba61c14ac37
theorem M7.Connectivity.one_mem_top : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)), (1 : ZMod N) ∈ H ↔ H = ⊤
  intro N inst H
  constructor
  · intro h
    apply le_antisymm le_top
    intro x hx
    simpa only [mul_one] using M7.Connectivity.scalar_mem N H 1 x h
  · intro h
    rw [h]
    trivial

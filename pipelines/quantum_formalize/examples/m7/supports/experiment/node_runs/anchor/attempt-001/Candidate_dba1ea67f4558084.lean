import FrozenTarget_dba1ea67f4558084
theorem M7.Supports.anchor : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ((M7.Supports.polynomial A).coeff 0 = 1 ↔ (0 : ZMod N) ∈ A)
  classical
  intro N inst A
  have h : (M7.Supports.polynomial A).coeff 0 = M7.Supports.indicator A (0 : ZMod N) := by
    simpa using M7.Supports.indicator_coefficient N A (0 : ZMod N)
  rw [h]
  by_cases hz : (0 : ZMod N) ∈ A <;> simp [M7.Supports.indicator, hz]

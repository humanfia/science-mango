import FrozenTarget_f9d7c8a6de7ad8cd
theorem M7.Supports.indicator_coefficient : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), ∀ i : ZMod N, (M7.Supports.polynomial A).coeff i.val = M7.Supports.indicator A i
  intro N inst A i
  rw [M7.Supports.coefficient N A i.val]
  unfold M7.Supports.indicator
  have h : (∃ j ∈ A, j.val = i.val) ↔ i ∈ A := by
    constructor
    · rintro ⟨j, hj, hji⟩
      have heq : j = i := ZMod.val_injective N hji
      exact heq ▸ hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  rw [h]

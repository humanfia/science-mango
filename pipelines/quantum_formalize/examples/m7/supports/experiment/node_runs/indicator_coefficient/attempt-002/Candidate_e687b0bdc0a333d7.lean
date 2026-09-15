import FrozenTarget_e687b0bdc0a333d7
theorem M7.Supports.indicator_coefficient : QuantumHarnessFrozenTarget := by
  classical
  intro N inst A i
  rw [M7.Supports.coefficient]
  unfold M7.Supports.indicator
  by_cases hi : i ∈ A
  · have hex : ∃ j ∈ A, j.val = i.val := ⟨i, hi, rfl⟩
    simp only [if_pos hex, if_pos hi]
  · have hnex : ¬ ∃ j ∈ A, j.val = i.val := by
      rintro ⟨j, hj, hval⟩
      have hji : j = i := ZMod.val_injective N hval
      exact hi (hji ▸ hj)
    simp only [if_neg hnex, if_neg hi]

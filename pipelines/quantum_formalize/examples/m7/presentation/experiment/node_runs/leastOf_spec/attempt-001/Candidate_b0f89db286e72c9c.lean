import FrozenTarget_b0f89db286e72c9c
theorem M7.Presentation.leastOf_spec : QuantumHarnessFrozenTarget := by
  classical
  intro α inst T
  by_cases h : T.Nonempty
  · constructor
    · intro x
      simp only [M7.Presentation.leastOf, dif_pos h, Option.some.injEq]
      constructor
      · intro hx
        rw [← hx]
        exact ⟨Finset.min'_mem T h, fun y hy => Finset.min'_le T y hy⟩
      · rintro ⟨hx, hmin⟩
        exact le_antisymm (Finset.min'_le T x hx) (hmin _ (Finset.min'_mem T h))
    · simp [M7.Presentation.leastOf, h, h.ne_empty]
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst T
    simp [M7.Presentation.leastOf]

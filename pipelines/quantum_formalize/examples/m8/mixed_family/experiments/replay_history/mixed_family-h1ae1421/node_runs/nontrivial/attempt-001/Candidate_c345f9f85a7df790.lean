import FrozenTarget_c345f9f85a7df790
theorem M8.MixedFamily.nontrivial : QuantumHarnessFrozenTarget := by
  change M8.MixedFamily.a ≠ 1 ∧ M8.MixedFamily.a ≠ 0 ∧ (M8.MixedFamily.a * M8.MixedFamily.b).natDegree = 3
  have ha : M8.MixedFamily.a.natDegree = 1 := by
    unfold M8.MixedFamily.a
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have hb : M8.MixedFamily.b.natDegree = 2 := by
    unfold M8.MixedFamily.b
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have ha1 : M8.MixedFamily.a ≠ 1 := by
    intro h
    rw [h] at ha
    simp at ha
  have ha0 : M8.MixedFamily.a ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hb0 : M8.MixedFamily.b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  refine ⟨ha1, ha0, ?_⟩
  rw [Polynomial.natDegree_mul ha0 hb0, ha, hb]

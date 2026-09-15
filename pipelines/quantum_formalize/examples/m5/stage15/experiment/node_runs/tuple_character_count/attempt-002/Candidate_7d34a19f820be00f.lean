import FrozenTarget_7d34a19f820be00f
theorem M5.TupleCharacter.tuple_character_count : QuantumHarnessFrozenTarget := by
  classical
  intro D n k f z
  have hself : z + z = 0 := by
    ext i
    exact (show ∀ a : ZMod 2, a + a = 0 by decide) (z i)
  have hz : ∀ u : M5.Character.BinaryVector D, z + u = 0 ↔ u = z := by
    intro u
    constructor
    · intro h
      apply add_left_cancel (a := z)
      exact h.trans hself.symm
    · rintro rfl
      exact hself
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← M5.Character.character_add, M5.Character.character_orthogonality, hz]
  simp [← Finset.sum_filter, M5.TupleCharacter.count, mul_comm]

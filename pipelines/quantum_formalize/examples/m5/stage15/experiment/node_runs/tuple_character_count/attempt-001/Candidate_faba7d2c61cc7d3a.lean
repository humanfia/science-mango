import FrozenTarget_faba7d2c61cc7d3a
theorem M5.TupleCharacter.tuple_character_count : QuantumHarnessFrozenTarget := by
  classical
  intro D n k f z
  have hself : z + z = 0 := by
    ext i
    change (z i + z i : ZMod 2) = 0
    have htwo : (2 : ZMod 2) = 0 := by decide
    simpa only [← two_mul, htwo, zero_mul]
  have hz (u : M5.Character.BinaryVector D) : z + u = 0 ↔ u = z := by
    constructor
    · intro h
      exact add_left_cancel (h.trans hself.symm)
    · intro h
      simpa only [h] using hself
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
   simp_rw [← M5.Character.character_add, M5.Character.character_orthogonality, hz]
  simp [M5.TupleCharacter.count, ← Finset.sum_filter, mul_comm]

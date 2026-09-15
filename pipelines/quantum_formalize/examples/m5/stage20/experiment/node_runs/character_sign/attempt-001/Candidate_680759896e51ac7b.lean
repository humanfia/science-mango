import FrozenTarget_680759896e51ac7b
theorem M5.ArithmeticSubset.character_sign : QuantumHarnessFrozenTarget := by
  intro P hP lam z
  unfold M5.QuotientCharacter.value M5.Character.value M5.Character.bitSign
  simp only [Finset.prod_pow_eq_pow_sum]
  exact neg_one_pow_eq_or ℤ _

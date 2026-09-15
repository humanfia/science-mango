import FrozenTarget_fe81d051e1376c38
theorem M5.ArithmeticTuple.R_exact : QuantumHarnessFrozenTarget := by
  intro P hP T d k z
  classical
  rw [M5.ArithmeticTuple.R, M5.ArithmeticTuple.numerator_exact]
  have h : (2 : ℤ) ^ P.natDegree ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [Int.mul_ediv_cancel_left, h]

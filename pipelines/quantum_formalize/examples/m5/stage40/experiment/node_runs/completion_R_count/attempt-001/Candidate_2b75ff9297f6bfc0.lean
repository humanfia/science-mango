import FrozenTarget_2b75ff9297f6bfc0
theorem M5.TupleCompletion.completion_R_count : QuantumHarnessFrozenTarget := by
  intro P hP Z T d k
  classical
  rw [M5.ArithmeticTuple.R_exact]
  simp only [M5.TupleCompletion.count, M5.TupleCompletion.divisibility_sum]

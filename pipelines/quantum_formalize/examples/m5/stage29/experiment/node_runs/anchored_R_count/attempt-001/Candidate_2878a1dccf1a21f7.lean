import FrozenTarget_2878a1dccf1a21f7
theorem M5.AnchoredTupleCount.anchored_R_count : QuantumHarnessFrozenTarget := by
  intro P hP T d k
  classical
  rw [M5.ArithmeticTuple.R_exact]
  simp only [M5.AnchoredTupleCount.count,
    M5.AnchoredTupleCount.anchored_tuple_divisibility]

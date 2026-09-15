import FrozenTarget_036af728ce9236d2
theorem M5.ArithmeticTuple.R_nonnegative : QuantumHarnessFrozenTarget := by
  change ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (T d k : ℕ) (z : AdjoinRoot P), 0 ≤ M5.ArithmeticTuple.R P hP T d k z
  intro P hP T d k z
  classical
  rw [M5.ArithmeticTuple.R_exact]
  exact Int.natCast_nonneg _

import FrozenTarget_94b04acf696f249a
theorem M5.ArithmeticSubset.binomial_coefficient : QuantumHarnessFrozenTarget := by
  intro P hP W k lam
  unfold M5.ArithmeticSubset.binomialTerm
  symm
  apply M5.Binomial.signed_coefficient_eval
  all_goals
    intros
    exact M5.ArithmeticSubset.character_sign P hP lam _

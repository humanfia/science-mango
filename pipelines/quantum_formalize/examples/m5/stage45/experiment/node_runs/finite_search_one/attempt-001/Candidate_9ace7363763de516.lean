import FrozenTarget_9ace7363763de516
theorem M5.PeriodSearch.finite_search_one : QuantumHarnessFrozenTarget := by
  change M5.PeriodSearch.finiteSearch (1 : M5.BinaryPolynomial) = 1
  exact (M5.PeriodSearch.finite_search_eq_period (1 : M5.BinaryPolynomial) Polynomial.monic_one (by simp)).trans M5.Period.period_one

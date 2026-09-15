import FrozenTarget_c285325493659414
theorem M5.Connectivity.divisor_moebius : QuantumHarnessFrozenTarget := by
  change ∀ n : ℕ, (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0
  intro n
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius, ArithmeticFunction.one_apply]

import FrozenTarget_8c62dccfaba4d2eb
theorem M7.ActualFactorized.exact_orbit_quotient : QuantumHarnessFrozenTarget := by
  intro N inst c E L R hE
  rw [M7.ActualFactorized.numerator_action_count N c E L R hE,
    M7.ActualFactorized.stabilizer_numerator N c]
  exact M7.ActualOrbit.exact_division N c (fun y => E y ∧ L y.1 ∧ R y.2)

import FrozenTarget_029f7a9f301cfb3c
theorem M6.ActualTransfer.shifted_coefficient_exact : QuantumHarnessFrozenTarget := by
  intro N inst a b P d
  simp [M6.ActualTransfer.shiftedCoefficient, M6.ActualTransfer.Q,
    Polynomial.coeff_sub, M6.Normalize.divide_coeff,
    M6.ActualTransfer.shift_division]

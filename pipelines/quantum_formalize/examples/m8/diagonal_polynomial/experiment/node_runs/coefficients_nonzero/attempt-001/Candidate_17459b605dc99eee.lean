import FrozenTarget_17459b605dc99eee
theorem M8.DiagonalPolynomial.coefficients_nonzero : QuantumHarnessFrozenTarget := by
  intro N inst p hp hdeg hzero
  apply hp
  have hrec := M6.Coordinates.block_reconstruct N p hdeg
  rw [hzero] at hrec
  simpa [M6.Coordinates.blockPolynomial] using hrec.symm

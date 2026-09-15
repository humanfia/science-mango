import FrozenTarget_83d28baa4b64a3dd
theorem M6.Coordinates.encode_polynomial : QuantumHarnessFrozenTarget := by
  intro N inst p hp
  change M6.Cyclic.image N (M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N p)) = M6.Cyclic.image N p
  rw [M6.Coordinates.block_reconstruct N p hp]

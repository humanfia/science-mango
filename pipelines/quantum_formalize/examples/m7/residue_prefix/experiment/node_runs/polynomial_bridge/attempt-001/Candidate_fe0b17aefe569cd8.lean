import FrozenTarget_fe0b17aefe569cd8
theorem M7.ResiduePrefix.polynomial_bridge : QuantumHarnessFrozenTarget := by
  classical
  intro N inst A
  unfold M7.ResiduePrefix.encode M7.Supports.natSupport M5.SupportPolynomial.ofSupport M7.Supports.polynomial
  rw [Finset.sum_image]
  intro a ha b hb hab
  have h := congrArg (fun k : ℕ => (k : ZMod N)) hab
  simpa only [ZMod.natCast_zmod_val] using h

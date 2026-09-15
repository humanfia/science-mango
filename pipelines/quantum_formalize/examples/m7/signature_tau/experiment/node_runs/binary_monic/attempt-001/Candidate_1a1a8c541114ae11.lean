import FrozenTarget_1a1a8c541114ae11
theorem M7.SignatureTau.binary_monic : QuantumHarnessFrozenTarget := by
  change ∀ F : M6.Cyclic.BinaryPolynomial, F ≠ 0 → F.Monic
  intro F hF
  change F.leadingCoeff = 1
  have hbinary : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  exact hbinary F.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hF)

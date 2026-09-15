import FrozenTarget_d91393ba03f28d7b
theorem M5.Period.quotient_finite : QuantumHarnessFrozenTarget := by
  change ∀ (F : M5.BinaryPolynomial), F.Monic → Finite (AdjoinRoot F)
  intro F hF
  letI : Module.Finite (ZMod 2) (AdjoinRoot F) := hF.finite_adjoinRoot
  apply Module.finite_of_finite (ZMod 2)

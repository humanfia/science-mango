import FrozenTarget_2bc13fc2ca058cf3
theorem M7.CompactStorage.unit_table_recovery : QuantumHarnessFrozenTarget := by
  intro N inst e u F hF
  change M7.CompactStorage.polynomialBits N (M7.RecipeSignature.signature (M7.Action.act (⟨u, false, 0, 0⟩ : M7.Action.Record N) e.representative)) = M7.CompactStorage.polynomialBits N F ↔ _
  constructor
  · intro h
    exact M7.CompactStorage.polynomial_injective N _ F
      (M7.CompactStorage.field_bounds N (M7.Action.act (⟨u, false, 0, 0⟩ : M7.Action.Record N) e.representative)).1 hF h
  · intro h
    exact congrArg (M7.CompactStorage.polynomialBits N) h

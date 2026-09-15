import FrozenTarget_ad4b759cf7f0bae7
theorem M6.Character.pinned_macwilliams : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P
  intro m D P
  classical
  simpa [M6.Character.weightedDual, M6.Character.weightedTransform,
    M6.Character.localTransform, M6.Character.pinnedTransform,
    M6.Character.pinnedCharacterFactor, M6.Character.pinned_product,
    M6.Character.pinnedMonomial, M6.Pinned.enumerator, Finset.sum_filter]
    using M6.Character.weighted_macwilliams m D (M6.Character.boundaryFactor P)

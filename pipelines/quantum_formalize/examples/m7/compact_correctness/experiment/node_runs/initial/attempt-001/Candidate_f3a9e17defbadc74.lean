import FrozenTarget_f3a9e17defbadc74
theorem M7.CompactCorrectness.initial : QuantumHarnessFrozenTarget := by
  intro N inst w E hE
  have hgood : M7.RecoveryInstance.GoodBases w (∅ : Finset (M7.Action.Recipe N)) := by
    simp [M7.RecoveryInstance.GoodBases, M7.CanonicalClasses.Normalized]
  refine ⟨hgood, ?_⟩
  rw [M7.CompactCorrectness.residual_eq]
  exact (M7.RecoveryInstance.count_card N w E ∅ hE hgood []).2.2

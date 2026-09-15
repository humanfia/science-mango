import M7CompactCorrectness

theorem M7.CompactCorrectness.residual_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (p : List Bool), M7.CompactGeneration.residual w E bases p = M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases p
  rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.CompactGeneration.emission w E bases).leaf = M7.RecoveryInstance.recoverLeaf w E bases ∧ insert (M7.CompactGeneration.emission w E bases).representative bases = M7.RecoveryInstance.insertedBases w E bases

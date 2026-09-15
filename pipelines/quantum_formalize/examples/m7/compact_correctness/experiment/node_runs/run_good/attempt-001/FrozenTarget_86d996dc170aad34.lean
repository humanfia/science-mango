import M7CompactCorrectness

theorem M7.CompactCorrectness.residual_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ (bases : Finset (M7.Action.Recipe N)) (p : List Bool), M7.CompactGeneration.residual w E bases p = M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases p
  rfl

theorem M7.CompactCorrectness.emission_eq : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), ∀ bases : Finset (M7.Action.Recipe N), (M7.CompactGeneration.emission w E bases).leaf = M7.RecoveryInstance.recoverLeaf w E bases ∧ insert (M7.CompactGeneration.emission w E bases).representative bases = M7.RecoveryInstance.insertedBases w E bases := by
  intro N inst w E bases
  constructor <;> rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial), M7.PrefixSector.ValidSector N E → ∀ (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), M7.RecoveryInstance.GoodBases w bases → root = M7.CompactGeneration.residual w E bases [] → M7.RecoveryInstance.GoodBases w (M7.CompactGeneration.run w E fuel bases root).finalBases

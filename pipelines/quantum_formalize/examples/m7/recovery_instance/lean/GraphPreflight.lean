import M7RecoveryInstance
import M7RecoveryPrefixAccepted
import M7PrefixOrbitAccepted
import M7DescentTraceAccepted

noncomputable def M7.RecoveryInstanceTarget.count_card : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, M7.RecoveryInstance.count w E bases p = (M7.RecoveryInstance.remaining w E bases p).card ∧ (M7.RecoveryInstance.count w E bases p).toNat = (M7.RecoveryInstance.remaining w E bases p).card ∧ 0 ≤ M7.RecoveryInstance.count w E bases p

noncomputable def M7.RecoveryInstanceTarget.count_partition : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, p.length < M7.PrefixBits.depth N → M7.RecoveryInstance.count w E bases p = M7.RecoveryInstance.count w E bases (p ++ [false]) + M7.RecoveryInstance.count w E bases (p ++ [true])

noncomputable def M7.RecoveryInstanceTarget.root_zero : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → (M7.RecoveryInstance.count w E bases [] = 0 ↔ M7.RecoveryPrefix.completed N w E [] ⊆ M7.OrbitResidual.covered bases)

noncomputable def M7.RecoveryInstanceTarget.positive_path : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → (M7.RecoveryInstance.word w E bases).length = M7.PrefixBits.depth N ∧ 0 < M7.RecoveryInstance.count w E bases (M7.RecoveryInstance.word w E bases) ∧ M7.DescentTrace.check (M7.RecoveryInstance.count w E bases) [] (M7.RecoveryInstance.path w E bases) = (true,2*M7.PrefixBits.depth N)

noncomputable def M7.RecoveryInstanceTarget.fresh_leaf : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.RecoveryInstance.remaining w E bases [] ∧ M7.RecoveryInstance.recoverLeaf w E bases ∈ M7.RecoveryPrefix.completed N w E (M7.RecoveryInstance.word w E bases)

noncomputable def M7.RecoveryInstanceTarget.insert_good : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → M7.RecoveryInstance.GoodBases w (M7.RecoveryInstance.insertedBases w E bases) ∧ M7.CanonicalOuter.canonical (M7.RecoveryInstance.recoverLeaf w E bases) ∉ bases

noncomputable def M7.RecoveryInstanceTarget.strict_decrease : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → 0 < M7.RecoveryInstance.count w E bases [] → (M7.RecoveryInstance.remaining w E (M7.RecoveryInstance.insertedBases w E bases) []).card < (M7.RecoveryInstance.remaining w E bases []).card ∧ (M7.RecoveryInstance.count w E (M7.RecoveryInstance.insertedBases w E bases) []).toNat < (M7.RecoveryInstance.count w E bases []).toNat


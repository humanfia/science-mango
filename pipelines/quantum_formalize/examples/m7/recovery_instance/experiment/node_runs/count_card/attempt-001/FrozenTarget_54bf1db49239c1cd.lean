import M7DescentTraceAccepted
import M7PrefixOrbitAccepted
import M7RecoveryInstance
import M7RecoveryPrefixAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, M7.RecoveryInstance.count w E bases p = (M7.RecoveryInstance.remaining w E bases p).card ∧ (M7.RecoveryInstance.count w E bases p).toNat = (M7.RecoveryInstance.remaining w E bases p).card ∧ 0 ≤ M7.RecoveryInstance.count w E bases p

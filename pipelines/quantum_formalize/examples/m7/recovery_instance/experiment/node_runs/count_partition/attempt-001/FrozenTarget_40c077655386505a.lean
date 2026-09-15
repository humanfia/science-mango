import M7DescentTraceAccepted
import M7PrefixOrbitAccepted
import M7RecoveryInstance
import M7RecoveryPrefixAccepted

theorem M7.RecoveryInstance.count_card : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, M7.RecoveryInstance.count w E bases p = (M7.RecoveryInstance.remaining w E bases p).card ∧ (M7.RecoveryInstance.count w E bases p).toNat = (M7.RecoveryInstance.remaining w E bases p).card ∧ 0 ≤ M7.RecoveryInstance.count w E bases p := by
  intro N inst w E bases hE hB p
  have h : M7.RecoveryInstance.count w E bases p = ((M7.RecoveryInstance.remaining w E bases p).card : ℤ) := by
    simpa only [M7.RecoveryInstance.count, M7.RecoveryInstance.remaining,
      M7.RecoveryPrefix.completed] using
      (M7.PrefixOrbit.residual_card N w E
        (M7.PrefixBits.A N p) (M7.PrefixBits.B N p)
        (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
        hE (M7.PrefixBits.base N (Nat.pos_of_ne_zero (NeZero.ne N)) p) bases
        (by first | exact hB.1 | exact hB.2)
        (by first | exact hB.1 | exact hB.2))
  refine ⟨h, ?_, ?_⟩
  · rw [h]
    simp
  · rw [h]
    exact Int.natCast_nonneg _
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.PrefixSector.ValidSector N E → M7.RecoveryInstance.GoodBases w bases → ∀ p : List Bool, p.length < M7.PrefixBits.depth N → M7.RecoveryInstance.count w E bases p = M7.RecoveryInstance.count w E bases (p ++ [false]) + M7.RecoveryInstance.count w E bases (p ++ [true])

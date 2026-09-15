import FrozenTarget_54bf1db49239c1cd
theorem M7.RecoveryInstance.count_card : QuantumHarnessFrozenTarget := by
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

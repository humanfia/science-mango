import FrozenTarget_2a15e5fb52e9d0f3
theorem M7.RecoveryInstance.root_zero : QuantumHarnessFrozenTarget := by
  intro N inst w E bases hE hB
  classical
  rw [(M7.RecoveryInstance.count_card N w E bases hE hB []).1]
  simp [M7.RecoveryInstance.remaining, M7.OrbitResidual.remaining,
    Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]

import FrozenTarget_5d4f2c370fb8fea6
theorem M7.RecoveryInstance.positive_path : QuantumHarnessFrozenTarget := by
  intro N inst w E bases hE hB hpos
  refine ⟨?_, ?_, ?_⟩
  · unfold M7.RecoveryInstance.word M7.RecoveryInstance.path
    rw [M7.DescentTrace.endpoint_recover, M5.BinaryRecovery.recover_length]
    simp
  · unfold M7.RecoveryInstance.word M7.RecoveryInstance.path
    rw [M7.DescentTrace.endpoint_recover]
    apply M5.BinaryRecovery.recover_positive
    · intro q hq
      apply M7.RecoveryInstance.count_partition N w E bases hE hB q
      simpa only [List.length_nil, Nat.zero_add] using hq
    · exact hpos
  · exact M7.DescentTrace.check_trace (M7.RecoveryInstance.count w E bases) [] (M7.PrefixBits.depth N)

import FrozenTarget_9b8a885db7b6a415
theorem M7.StreamingCost.record_cardinality : QuantumHarnessFrozenTarget := by
  intro N inst
  constructor <;>
    simp [M7.StreamingCost.recordCount, M7.Action.record_card,
      ZMod.card_units_eq_totient, pow_two, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] <;> ring

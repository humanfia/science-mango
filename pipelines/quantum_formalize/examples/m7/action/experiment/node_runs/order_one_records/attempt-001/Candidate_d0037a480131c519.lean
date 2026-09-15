import FrozenTarget_d0037a480131c519
theorem M7.Action.order_one_records : QuantumHarnessFrozenTarget := by
  change Fintype.card (M7.Action.Record 1) = 2
  simpa using (M7.Action.record_card 1)

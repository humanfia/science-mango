import FrozenTarget_bf620f1daa171bef
theorem M7.FinalResources.comparison : QuantumHarnessFrozenTarget := by
  intro N w inst E hw hwN hE q
  have h := (M7.StreamingCost.scan_bound (M7.GeneratedFamily.size N w E) N q (M7.GeneratedFamily.family N w E)).2
  rw [(M7.StreamingCost.record_cardinality N).2] at h
  have hcharge := Nat.mul_le_mul_right (M7.FinalResources.objectiveBits q (M7.GeneratedFamily.family N w E)) (Nat.mul_le_mul_right (2 * (q.objectives.length + 1)) h)
  simpa [M7.FinalResources.comparisonCharge, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcharge

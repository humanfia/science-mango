import FrozenTarget_388208e8ac318022
theorem M5.PhysicalBridge.repaired_exponent_cutoff : QuantumHarnessFrozenTarget := by
  change ∀ w T e δ k : ℕ, 0 < T → e < w * T → δ < w * T → k < w + δ → e + k * T < M5.packingCutoff w T
  intro w T e δ k hT he hδ hk
  have hk_bound : k + 2 ≤ w + w * T := by omega
  have hprod := Nat.mul_le_mul_right T hk_bound
  unfold M5.packingCutoff
  nlinarith

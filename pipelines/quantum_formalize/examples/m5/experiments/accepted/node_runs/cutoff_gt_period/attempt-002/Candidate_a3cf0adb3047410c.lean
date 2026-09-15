import FrozenTarget_a3cf0adb3047410c
theorem M5.cutoff_gt_period : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T
  intro w T hw hT
  unfold M5.packingCutoff
  have h₁ : 2 * T ≤ w * T := Nat.mul_le_mul_right T hw
  have h₂ : w * T * 1 ≤ w * T * (T + 2) :=
    Nat.mul_le_mul_left (w * T) (by omega : 1 ≤ T + 2)
   omega

import M5Foundation

theorem M5.packed_range : ∀ (w T r j : ℕ), r < T → j < w → M5.packedExponent T r j < w * T := by
  intro w T r j hr hj
  change r + j * T < w * T
  have hjw : j + 1 ≤ w := Nat.succ_le_of_lt hj
  calc
    r + j * T < T + j * T := Nat.add_lt_add_right hr _
    _ = (j + 1) * T := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ w * T := Nat.mul_le_mul_right T hjw

theorem M5.repair_above_packing : ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T := by
  change ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T
  intro w T e k hT hwk
  exact Nat.le_trans (Nat.mul_le_mul_right T hwk) (Nat.le_add_left (k * T) e)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T r j e k : ℕ), r < T → j < w → w ≤ k → M5.packedExponent T r j ≠ e + k * T

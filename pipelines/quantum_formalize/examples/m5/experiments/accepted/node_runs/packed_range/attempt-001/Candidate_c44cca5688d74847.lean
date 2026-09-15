import FrozenTarget_c44cca5688d74847
theorem M5.packed_range : QuantumHarnessFrozenTarget := by
  intro w T r j hr hj
  change r + j * T < w * T
  have hjw : j + 1 ≤ w := Nat.succ_le_of_lt hj
  calc
    r + j * T < T + j * T := Nat.add_lt_add_right hr _
    _ = (j + 1) * T := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ w * T := Nat.mul_le_mul_right T hjw

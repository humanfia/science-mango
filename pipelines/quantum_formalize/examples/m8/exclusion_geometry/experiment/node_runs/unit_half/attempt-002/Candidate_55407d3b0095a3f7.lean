import FrozenTarget_55407d3b0095a3f7
theorem M8.ExclusionGeometry.unit_half : QuantumHarnessFrozenTarget := by
  intro N _ h u hN
  have hc := ZMod.val_coe_unit_coprime u
  rw [hN, Nat.coprime_mul_iff_right] at hc
  obtain ⟨k, hk⟩ := Nat.coprime_two_right.mp hc.1
  have hv : (u : ZMod N).val = 2 * k + 1 := by omega
  have hz : (2 : ZMod N) * (h : ZMod N) = 0 := by
    calc
      (2 : ZMod N) * (h : ZMod N) = ((2 * h : ℕ) : ZMod N) := by push_cast; rfl
      _ = (N : ZMod N) := congrArg (fun n : ℕ => (n : ZMod N)) hN.symm
      _ = 0 := by simp
  rw [← ZMod.natCast_zmod_val (u : ZMod N), hv]
  push_cast
  calc
    (2 * (k : ZMod N) + 1) * (h : ZMod N) = (k : ZMod N) * (2 * (h : ZMod N)) + (h : ZMod N) := by ring
    _ = (h : ZMod N) := by rw [hz]; simp

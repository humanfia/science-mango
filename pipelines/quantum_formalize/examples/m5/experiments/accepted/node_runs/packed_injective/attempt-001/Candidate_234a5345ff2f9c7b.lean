import FrozenTarget_234a5345ff2f9c7b
theorem M5.packed_injective : QuantumHarnessFrozenTarget := by
  change ∀ (T r s j k : ℕ), r < T → s < T → M5.packedExponent T r j = M5.packedExponent T s k → r = s ∧ j = k
  intro T r s j k hr hs h
  have hrs : r = s := by
    calc
      r = M5.packedExponent T r j % T := (M5.packed_residue T r j hr).symm
      _ = M5.packedExponent T s k % T := congrArg (fun n : ℕ => n % T) h
      _ = s := M5.packed_residue T s k hs
  subst s
  refine ⟨rfl, ?_⟩
  have hT : T ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le r) hr)
  have hm : j * T = k * T := by
    simpa [M5.packedExponent, Nat.mul_comm] using h
  exact mul_right_cancel₀ hT hm

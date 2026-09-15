import FrozenTarget_e389d5d5d245b4a3
theorem M6.Transfer.indexed_array_correct_resources : QuantumHarnessFrozenTarget := by
  intro R N inst W hRN hmass hdegree
  classical
  have hsmall (i : ℕ) (hi : i < N) : (8 : ℕ) ^ (i + 1) ≤ 2 ^ R * 8 ^ N := by
    have hexp : i + 1 ≤ N := Nat.succ_le_of_lt hi
    have hpow : 1 ≤ (2 : ℕ) ^ R := Nat.succ_le_of_lt (pow_pos (by decide) R)
    calc
      (8 : ℕ) ^ (i + 1) ≤ 8 ^ N := Nat.pow_le_pow_right (by decide) hexp
      _ = 1 * 8 ^ N := (one_mul _).symm
      _ ≤ 2 ^ R * 8 ^ N := Nat.mul_le_mul_right _ hpow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M6.Transfer.scalar_trace_polynomial R N W hdegree).trans
      (M6.Transfer.array_trace_inputs R N (Polynomial ℤ) W)
  · exact M6.Transfer.actual_trace_work_bound R N hRN
  · exact M6.Transfer.actual_trace_storage_bound R N hRN
  · exact M6.Transfer.actual_address_capacity R N hRN
  · intro start i hi k addr
    unfold M6.Transfer.FitsSigned
    have h := M6.Transfer.actual_layer_intermediates R N W start i k addr hmass hdegree
    exact lt_of_le_of_lt (le_trans h.1 (hsmall i hi))
      (M6.Transfer.actual_signed_capacity R N)
  · intro start i hi e
    unfold M6.Transfer.FitsSigned
    have h := M6.Transfer.actual_layer_intermediates R N W start i 0
      (start, ⟨0, by omega⟩) hmass hdegree
    exact lt_of_le_of_lt (le_trans (h.2 e) (hsmall i hi))
      (M6.Transfer.actual_signed_capacity R N)
  · intro k d
    unfold M6.Transfer.FitsSigned
    exact lt_of_le_of_lt
      (M6.Transfer.actual_trace_intermediates R N W k d hmass hdegree)
      (M6.Transfer.actual_signed_capacity R N)

import FrozenTarget_1fad311951708a9f
theorem M6.Transfer.indexed_array_correct_resources : QuantumHarnessFrozenTarget := by
  intro R N inst W hRN hmass hdegree
  classical
  have hscale (i : ℕ) (hi : i < N) :
      8 ^ (i + 1) ≤ 2 ^ R * 8 ^ N := by
    calc
      8 ^ (i + 1) ≤ 8 ^ N := by
        gcongr
        omega
      _ ≤ 2 ^ R * 8 ^ N := by
        have hp : 0 < (2 : ℕ) ^ R := by positivity
        nlinarith
  have hfit (z : ℤ) (hz : z.natAbs ≤ 2 ^ R * 8 ^ N) :
      M6.Transfer.FitsSigned R N z := by
    exact lt_of_le_of_lt hz (M6.Transfer.actual_signed_capacity R N)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M6.Transfer.scalar_trace_polynomial R N W hdegree).trans
      (M6.Transfer.array_trace_inputs R N (Polynomial ℤ) W)
  · exact M6.Transfer.actual_trace_work_bound R N hRN
  · exact M6.Transfer.actual_trace_storage_bound R N hRN
  · exact M6.Transfer.actual_address_capacity R N hRN
  · intro start i hi k addr
    apply hfit
    exact le_trans
      (M6.Transfer.actual_layer_intermediates R N W start i k addr hmass hdegree).1
      (hscale i hi)
  · intro start i hi e
    have hb := M6.Transfer.actual_layer_intermediates R N W start i 0
      (start, ⟨0, by omega⟩) hmass hdegree
    apply hfit
    exact le_trans (hb.2 e) (hscale i hi)
  · intro k d
    apply hfit
    exact M6.Transfer.actual_trace_intermediates R N W k d hmass hdegree

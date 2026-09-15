import FrozenTarget_6093a09984f1948c
theorem M6.Final.zero_span_correct : QuantumHarnessFrozenTarget := by
  change M6.Final.ZeroSpanCorrect
  refine ⟨M6.ZeroSpan.anchored_zero, M6.ZeroSpan.connected_zero, M6.ZeroSpan.boundary_loops, M6.ZeroSpan.character_loops, M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero, ?_⟩
  intro N inst
  unfold M6.ActualTransfer.Q
  rw [M6.ZeroSpan.boundary_trace_zero, M6.ZeroSpan.character_trace_zero]
  have hf : M6.ActualCounts.f N 1 1 = 0 := by
    unfold M6.ActualCounts.f
    rw [M6.ZeroSpan.signature_one]
    simp
  change M6.Normalize.divide ((2 : ℤ)^N) (Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N) - M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N 1 1)) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) = 0
  rw [hf]
  simp only [pow_zero]
  rw [M6.Normalize.divide_scaled _ _ (pow_ne_zero _ (by norm_num))]
  have h1 := M6.Normalize.divide_scaled (1 : ℤ) (((1 : Polynomial ℤ) + Polynomial.X^2)^N) (by norm_num)
  simp only [map_one, one_mul] at h1
  rw [h1]
  exact sub_self _

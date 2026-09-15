import FrozenTarget_04828fe98e4353b3
theorem M6.Transfer.actual_trace_storage_bound : QuantumHarnessFrozenTarget := by
  change ∀ R N : ℕ, R < N → M6.Transfer.actualTraceStorage R N ≤ 4096 * N^2 * 2^R
  intro R N hRN
  have hN : 1 ≤ N := by omega
  have hs : 1 ≤ (2 : ℕ)^R := by positivity
  have ha : M6.Transfer.actualAddressBits R N ≤ 21*N := by
    unfold M6.Transfer.actualAddressBits
    omega
  have hc : M6.Transfer.coefficientBits R N ≤ 6*N := by
    unfold M6.Transfer.coefficientBits
    omega
  have hlen : (M6.Transfer.scatterEventList R N).length = 6*(2*N+1)*2^R := by
    classical
    simp [M6.Transfer.scatterEventList, M6.Transfer.ScatterEvent,
      Fintype.card_prod, M6.Transfer.state_count, M6.Transfer.Bit] <;> ring
  have hl : (M6.Transfer.scatterEventList R N).length ≤ 18*N*2^R := by
    have hm := Nat.mul_le_mul_right (6*2^R) hN
    nlinarith only [hlen, hm]
  have hr : 4*M6.Transfer.actualAddressBits R N + 8 ≤ 92*N := by omega
  have he : (M6.Transfer.scatterEventList R N).length *
      (4*M6.Transfer.actualAddressBits R N + 8) ≤ 1656*N^2*2^R := by
    have hm := Nat.mul_le_mul hl hr
    nlinarith only [hm]
  have hsq : N ≤ N^2 := by nlinarith only [hN]
  have hscale : N ≤ N^2*2^R := by
    have hm := Nat.mul_le_mul_left (N^2) hs
    nlinarith only [hsq, hm]
  have hscratch : 64*(M6.Transfer.coefficientBits R N +
      M6.Transfer.actualAddressBits R N) ≤ 1728*N^2*2^R := by
    have hb : 64*(M6.Transfer.coefficientBits R N +
        M6.Transfer.actualAddressBits R N) ≤ 1728*N := by omega
    nlinarith only [hb, hscale]
  have hextra : 4*N ≤ 4*N^2*2^R := by
    nlinarith only [hscale]
  have hbase := M6.Transfer.trace_storage_bound R N hRN
  unfold M6.Transfer.actualTraceStorage
  nlinarith only [hbase, he, hscratch, hextra]

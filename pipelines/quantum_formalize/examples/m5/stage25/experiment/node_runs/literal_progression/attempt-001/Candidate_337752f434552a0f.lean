import FrozenTarget_337752f434552a0f
theorem M5.PhysicalOrder.literal_progression : QuantumHarnessFrozenTarget := by
  intro A B w T F hw hT hAcard hBcard hA hB hAbound hBbound hg hF j hj
  have hcut : w * T < M5.packingCutoff w T := by
    unfold M5.packingCutoff
    nlinarith [Nat.mul_pos (by omega : 0 < w) hT]
  have hN : 0 < T + j * M5.PhysicalOrder.supportPeriod A B := by omega
  have hArange : ∀ a ∈ A, a < T + j * M5.PhysicalOrder.supportPeriod A B := by
    intro a ha
    exact lt_of_lt_of_le (hAbound a ha) hj
  have hBrange : ∀ b ∈ B, b < T + j * M5.PhysicalOrder.supportPeriod A B := by
    intro b hb
    exact lt_of_lt_of_le (lt_trans (hBbound b hb) hcut) hj
  have hconn : M5.Connectivity.supportGcd (T + j * M5.PhysicalOrder.supportPeriod A B) A B = 1 := by
    unfold M5.RepairSupport.combinedGcd at hg
    simpa [M5.Connectivity.supportGcd, Nat.gcd_assoc, hg]
  have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) (T + j * M5.PhysicalOrder.supportPeriod A B) = F := by
    rw [M5.Signature.exact_signature_lift _ _ T (M5.PhysicalOrder.supportPeriod A B) j
      (M5.PhysicalOrder.period_control A B w T hw hT hA hB hBbound).2.2]
    exact hF
  unfold M5.PhysicalOrder.realizes
  simp_all only [Finset.subset_iff, Finset.mem_range]
  <;> aesop

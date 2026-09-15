import FrozenTarget_e1c2fe77827bb88d
theorem M5.ArithmeticWorkflow.order_count_iff : QuantumHarnessFrozenTarget := by
  classical
  intro N w F hN hw hF hF0
  by_cases hd : F ∣ M5.cyclicModulus N
  · simpa [M5.PhysicalOrder.realizes, Finset.subset_iff, Finset.mem_range,
      hN, and_assoc, and_left_comm, and_comm] using
      (M5.OrderCount.C_positive_iff_realization N w F hN hw hF hd)
  · have hC : M5.OrderCount.C N w F = 0 := by
      simp [M5.OrderCount.C, hd]
    rw [hC]
    constructor
    · intro h
      exact (lt_irrefl 0 h).elim
    · rintro ⟨S, U, h⟩
      have hs : M5.completeSignature (M5.SupportPolynomial.ofSupport S)
          (M5.SupportPolynomial.ofSupport U) N = F := by
        unfold M5.PhysicalOrder.realizes at h
        tauto
      have hf : F ∣ M5.cyclicModulus N := by
        rw [← hs]
        unfold M5.completeSignature
        exact gcd_dvd_right _ _
      exact (hd hf).elim

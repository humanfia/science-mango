import FrozenTarget_2e3c608e7dfb69b8
theorem M5.ArithmeticWorkflow.order_count_iff : QuantumHarnessFrozenTarget := by
  intro N w F hN hw hF hF0
  classical
  by_cases hd : F ∣ M5.cyclicModulus N
  · rw [M5.OrderCount.C_positive_iff_realization N w F hN hw hF hd]
    constructor
    · rintro ⟨A, B, hA, hB, hAz, hBz, hAc, hBc, hg, hs⟩
      exact ⟨A, B, hN, hAc, hBc, hAz, hBz,
        (fun e he => Finset.mem_range.mp (hA he)),
        (fun e he => Finset.mem_range.mp (hB he)), hg, hs⟩
    · rintro ⟨A, B, hR⟩
      rcases hR with ⟨_, hAc, hBc, hAz, hBz, hA, hB, hg, hs⟩
      exact ⟨A, B, (fun e he => Finset.mem_range.mpr (hA e he)),
        (fun e he => Finset.mem_range.mpr (hB e he)), hAz, hBz, hAc, hBc, hg, hs⟩
  · have hC : M5.OrderCount.C N w F = 0 := by
      simp only [M5.OrderCount.C, hd, false_and, ite_false]
    rw [hC]
    constructor
    · exact fun h => (lt_irrefl 0 h).elim
    · rintro ⟨A, B, hR⟩
      rcases hR with ⟨_, _, _, _, _, _, _, _, hs⟩
      have hf : F ∣ M5.cyclicModulus N := by
        rw [← hs]
        exact EuclideanDomain.gcd_dvd_right
          (EuclideanDomain.gcd (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B))
          (M5.cyclicModulus N)
      exact (hd hf).elim

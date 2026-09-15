import FrozenTarget_49c8f53c9f073d5a
theorem M5.ArithmeticWorkflow.order_count_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (0 < M5.OrderCount.C N w F ↔ ∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)
  intro N w F hN hw hF hF0
  classical
  by_cases hdiv : F ∣ M5.cyclicModulus N
  · have h := M5.OrderCount.C_positive_iff_realization N w F hN hw hF hdiv
    simp only [Finset.subset_iff, Finset.mem_range] at h
    simpa [M5.PhysicalOrder.realizes, hN, and_assoc, and_left_comm, and_comm] using h
  · have hzero : M5.OrderCount.C N w F = 0 := by
      simp [M5.OrderCount.C, hdiv]
    rw [hzero]
    constructor
    · intro h
      exact (lt_irrefl 0 h).elim
    · rintro ⟨S, U, hreal⟩
      have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport S)
          (M5.SupportPolynomial.ofSupport U) N = F := by
        unfold M5.PhysicalOrder.realizes at hreal
        tauto
      have hd : F ∣ M5.cyclicModulus N := by
        rw [← hsig]
        unfold M5.completeSignature
        first
        | exact gcd_dvd_right _ _
        | exact dvd_trans (gcd_dvd_right _ _) (gcd_dvd_right _ _)
      exact (hdiv hd).elim

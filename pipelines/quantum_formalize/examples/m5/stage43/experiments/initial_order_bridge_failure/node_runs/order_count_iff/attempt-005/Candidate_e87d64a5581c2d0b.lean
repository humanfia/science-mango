import FrozenTarget_e87d64a5581c2d0b
theorem M5.ArithmeticWorkflow.order_count_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (0 < M5.OrderCount.C N w F ↔ ∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)
  intro N w F hN hw hF hF0
  classical
  by_cases hd : F ∣ M5.cyclicModulus N
  · simpa [M5.PhysicalOrder.realizes, Finset.subset_iff, Finset.mem_range,
      hN, hw, and_assoc, and_left_comm, and_comm] using
      (M5.OrderCount.C_positive_iff_realization N w F hN hw hF hd)
  · have hzero : M5.OrderCount.C N w F = 0 := by
      simp [M5.OrderCount.C, hd]
    rw [hzero]
    constructor
    · intro h
      exact False.elim ((lt_irrefl 0) h)
    · rintro ⟨S, U, h⟩
      have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport S)
          (M5.SupportPolynomial.ofSupport U) N = F := by
        unfold M5.PhysicalOrder.realizes at h
        tauto
      exfalso
      apply hd
      rw [← hsig]
      unfold M5.completeSignature
      first
      | exact gcd_dvd_right _ _
      | exact Polynomial.gcd_dvd_right _ _
      | exact dvd_trans (gcd_dvd_right _ _) (gcd_dvd_right _ _)

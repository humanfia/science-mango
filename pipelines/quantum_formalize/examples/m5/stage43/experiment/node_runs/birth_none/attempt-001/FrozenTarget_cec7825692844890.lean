import M5ArithmeticWorkflowReady

theorem M5.ArithmeticWorkflow.order_count_iff : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F.coeff 0 = 1 → (0 < M5.OrderCount.C N w F ↔ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)) := by
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

theorem M5.ArithmeticWorkflow.birth_exact : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → 0 < M5.ResidueCount.A w F → ∃ b : ℕ, M5.ArithmeticWorkflow.birth w F = some b ∧ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes b w F S U) ∧ ∀ N : ℕ, (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U) → b ≤ N := by
  intro w F hw hF hF0 hA
  classical
  unfold M5.ArithmeticWorkflow.birth
  apply M5.BirthSearch.birth_exact _ _ _ _
    (fun N => ∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)
  · intro N hN
    rcases hN with ⟨S, U, hR⟩
    rcases M5.OrderBoundary.signature_lower_bounds N w F S U hF hF0 hR with ⟨hd, hwN, hdeg⟩
    exact ⟨max_le hwN (by omega), hd⟩
  · intro N hlower hd
    have hN : 0 < N := by omega
    exact M5.ArithmeticWorkflow.order_count_iff N w F hN (by omega) hF hF0
  · obtain ⟨S, U, N, E, hE, hbound, hR⟩ :=
      M5.GlobalCriterion.positive_bounded_progression w F hw hF hF0 hA
    refine ⟨N, Nat.le_of_lt hbound, S, U, ?_⟩
    simpa using hR 0
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → (M5.ArithmeticWorkflow.birth w F = none ↔ M5.ResidueCount.A w F = 0)

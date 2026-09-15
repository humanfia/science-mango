import FrozenTarget_29e4cdcdb703fbd5
theorem M7.ArithmeticLoops.character_visits : QuantumHarnessFrozenTarget := by
  classical
  intro N hN w E A B hE
  change M7.ArithmeticLoops.characterVisits N w E A B ≤ _
  unfold M7.ArithmeticLoops.characterVisits
  split_ifs with hguard
  · have hinner : ∀ F ∈ E,
        (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
          2 * Fintype.card (M5.Character.BinaryVector (F * (∏ p ∈ S, p)).natDegree)) ≤
        2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
      intro F hFE
      have hF : F.Monic ∧ F ∣ M5.cyclicModulus N := by
        have hv := hE
        unfold M7.PrefixSector.ValidSector at hv
        aesop
      calc
        _ ≤ ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
            2 * 2 ^ N := by
          apply Finset.sum_le_sum
          intro S hS
          rw [M7.ArithmeticLoops.character_card]
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by omega)
          exact (M7.ArithmeticLoops.exclusion_cap N hN F S hF.1 hF.2
            (Finset.mem_powerset.mp hS)).2
        _ = 2 ^ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).card *
            (2 * 2 ^ N) := by
          simp
        _ ≤ 2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
          apply Nat.mul_le_mul_right
          exact Nat.pow_le_pow_right (by omega)
            (M7.ArithmeticLoops.factor_card N hN F hF.1 hF.2)
    calc
      _ ≤ ∑ F ∈ E, M7.ArithmeticLoops.divisorCount N *
          (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) := by
        apply Finset.sum_le_sum
        intro F hFE
        calc
          _ ≤ ∑ _d ∈ (M5.Connectivity.supportGcd N A B).divisors,
              2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
            apply Finset.sum_le_sum
            intro d hd
            exact hinner F hFE
          _ = (M5.Connectivity.supportGcd N A B).divisors.card *
              (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) := by
            simp
          _ ≤ M7.ArithmeticLoops.divisorCount N *
              (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) :=
            Nat.mul_le_mul_right _ (M7.ArithmeticLoops.divisor_card N hN A B)
      _ = 2 * E.card * M7.ArithmeticLoops.divisorCount N *
          2 ^ (M7.ArithmeticLoops.factorCount N + N) := by
        simp only [Finset.sum_const, smul_eq_mul, pow_add]
        ring
  · exact Nat.zero_le _

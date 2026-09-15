import FrozenTarget_d8ff16fe619d756d
theorem M7.ScalarWork.prefix_bound : QuantumHarnessFrozenTarget := by
    classical
    intro N w A B WA WB hN hw hBase F hF hFd
    change M7.ScalarWork.prefixWork N w F A B WA WB ≤ _
    have hWA : WA ⊆ Finset.range N := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    have hWB : WB ⊆ Finset.range N := by
      unfold M7.PrefixCompleted.Base at hBase
      tauto
    have hrestricted : ∀ W : Finset ℕ, W ⊆ Finset.range N → ∀ d : ℕ,
        (M5.ConditionalCount.restricted W d).card ≤ N := by
      intro W hW d
      calc
        (M5.ConditionalCount.restricted W d).card ≤ W.card := by
          unfold M5.ConditionalCount.restricted
          exact Finset.card_filter_le _ _
        _ ≤ N := by
          simpa using Finset.card_le_card hW
    let R := M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F
    let C : ℕ := 1024 * N^4 * 2^N
    have hcost : ∀ d : ℕ, ∀ S ∈ R.powerset,
        16 + 2^(F * (∏ p ∈ S, p)).natDegree *
          (M7.ScalarWork.term (F * (∏ p ∈ S, p)).natDegree
            (M5.ConditionalCount.restricted WA d) (w - A.card) +
           M7.ScalarWork.term (F * (∏ p ∈ S, p)).natDegree
            (M5.ConditionalCount.restricted WB d) (w - B.card)) ≤ C := by
      intro d S hS
      have hdeg := (M7.ArithmeticLoops.exclusion_cap N hN F S hF hFd
        (Finset.mem_powerset.mp hS)).2
      have ha := M7.ScalarWork.term_bound N _ _ _ hN hdeg
        (show w - A.card ≤ N by omega) (hrestricted WA hWA d)
      have hb := M7.ScalarWork.term_bound N _ _ _ hN hdeg
        (show w - B.card ≤ N by omega) (hrestricted WB hWB d)
      have hp : 2^(F * (∏ p ∈ S, p)).natDegree ≤ (2 : ℕ)^N := by
        gcongr
        norm_num
      have hmul := Nat.mul_le_mul hp (Nat.add_le_add ha hb)
      have hpos : 0 < N^4 * (2 : ℕ)^N := by positivity
      dsimp [C]
      nlinarith only [hmul, hpos]
    have hdiv := M7.ArithmeticLoops.divisor_card N hN A B
    have hfac := M7.ArithmeticLoops.factor_card N hN F hF hFd
    have hpow : R.powerset.card ≤ 2^M7.ArithmeticLoops.factorCount N := by
      rw [Finset.card_powerset]
      change 2^R.card ≤ 2^M7.ArithmeticLoops.factorCount N
      have hr : R.card ≤ M7.ArithmeticLoops.factorCount N := hfac
      gcongr
      norm_num
    unfold M7.ScalarWork.prefixWork
    split_ifs with hguard
    · calc
        _ ≤ ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
            ∑ S ∈ R.powerset, C := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro S hS
          exact hcost d S hS
        _ = (M5.Connectivity.supportGcd N A B).divisors.card *
            (R.powerset.card * C) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ M7.ArithmeticLoops.divisorCount N *
            (2^M7.ArithmeticLoops.factorCount N * C) :=
          Nat.mul_le_mul hdiv (Nat.mul_le_mul_right C hpow)
        _ = 1024 * N^4 * M7.ArithmeticLoops.divisorCount N *
            2^(M7.ArithmeticLoops.factorCount N + N) := by
          dsimp [C]
          rw [pow_add]
          ring
    · exact Nat.zero_le _

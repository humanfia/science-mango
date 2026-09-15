import FrozenTarget_58e7d66fd2ca7341
theorem M7.ScalarWork.prefix_bound : QuantumHarnessFrozenTarget := by
  classical
  intro N w A B WA WB hN hw hBase F hF hFd
  change M7.ScalarWork.prefixWork N w F A B WA WB ≤ _
  have hWA : WA ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    aesop
  have hWB : WB ⊆ Finset.range N := by
    unfold M7.PrefixCompleted.Base at hBase
    aesop
  have hrestricted : ∀ (W : Finset ℕ), W ⊆ Finset.range N → ∀ d,
      (M5.ConditionalCount.restricted W d).card ≤ N := by
    intro W hW d
    have hs : M5.ConditionalCount.restricted W d ⊆ W := by
      intro i hi
      simp only [M5.ConditionalCount.restricted, Finset.mem_filter] at hi
      exact hi.1
    have hc := Finset.card_le_card (hs.trans hW)
    simpa only [Finset.card_range] using hc
  let R := M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F
  let C := 1024 * N^4 * 2^N
  have hcost : ∀ d, ∀ S ∈ R.powerset,
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
    have ht : M7.ScalarWork.term (F * (∏ p ∈ S, p)).natDegree
            (M5.ConditionalCount.restricted WA d) (w - A.card) +
         M7.ScalarWork.term (F * (∏ p ∈ S, p)).natDegree
            (M5.ConditionalCount.restricted WB d) (w - B.card) ≤ 256 * N^4 := by
      omega
    have hm := Nat.mul_le_mul hp ht
    have hpos : 0 < N^4 * (2 : ℕ)^N := by positivity
    dsimp [C]
    nlinarith only [hm, hpos]
  have hdiv := M7.ArithmeticLoops.divisor_card N hN A B
  have hfac := M7.ArithmeticLoops.factor_card N hN F hF hFd
  have hpow : R.powerset.card ≤ 2^(M7.ArithmeticLoops.factorCount N) := by
    rw [Finset.card_powerset]
    dsimp [R]
    gcongr
  unfold M7.ScalarWork.prefixWork
  split_ifs with hguard
  · calc
      _ ≤ (M5.Connectivity.supportGcd N A B).divisors.sum
          (fun _ => R.powerset.sum (fun _ => C)) := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro S hS
        exact hcost d S hS
      _ = (M5.Connectivity.supportGcd N A B).divisors.card *
          (R.powerset.card * C) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M7.ArithmeticLoops.divisorCount N *
          (2^(M7.ArithmeticLoops.factorCount N) * C) := by
        exact Nat.mul_le_mul hdiv (Nat.mul_le_mul_right C hpow)
      _ = _ := by
        dsimp [C]
        rw [pow_add]
        ring
  · exact Nat.zero_le _

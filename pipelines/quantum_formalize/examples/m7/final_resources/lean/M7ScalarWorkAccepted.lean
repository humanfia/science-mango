import M7ScalarWork

theorem M7.ScalarWork.mask_positions : ∀ (N : ℕ) [NeZero N], M7.ScalarWork.maskPositions N = 4 * Fintype.card ((ZMod N)ˣ) * N^2 := by
  intro N inst
  classical
  simp [M7.ScalarWork.maskPositions, M7.ActualFactorized.Outer, Fintype.card_prod, ZMod.card] <;> ring

theorem M7.ScalarWork.term_bound : ∀ (N D k : ℕ) (W : Finset ℕ), 0 < N → D ≤ N → k ≤ N → W.card ≤ N → M7.ScalarWork.term D W k ≤ 128 * N^4 := by
  intro N D k W hN hD hk hW
  change M7.ScalarWork.term D W k ≤ 128 * N^4
  simp only [M7.ScalarWork.term, M7.ScalarWork.negative,
    M7.ScalarWork.character, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hneg : W.card * (2 + (1 + 4 * D)) ≤ N * (3 + 4 * N) :=
    Nat.mul_le_mul hW (by omega)
  have hfactor : 8 + 2 * (W.card * (2 + (1 + 4 * D))) ≤
      8 + 2 * (N * (3 + 4 * N)) := by omega
  have hprod := Nat.mul_le_mul (show k + 1 ≤ N + 1 by omega) hfactor
  have h12 : N ≤ N^2 := by nlinarith
  have h23 : N^2 ≤ N^3 := by
    nlinarith only [Nat.mul_le_mul_left N h12]
  have h34 : N^3 ≤ N^4 := by
    nlinarith only [Nat.mul_le_mul_left N h23]
  nlinarith only [hprod, hD, hN, h12, h23, h34]

theorem M7.ScalarWork.prefix_bound : ∀ (N w : ℕ) (A B WA WB : Finset ℕ), 0 < N → w ≤ N → M7.PrefixCompleted.Base N A B WA WB → ∀ F : M5.BinaryPolynomial, F.Monic → F ∣ M5.cyclicModulus N → M7.ScalarWork.prefixWork N w F A B WA WB ≤ 1024 * N^4 * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N) := by
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

theorem M7.ScalarWork.sector_bound : ∀ (N w : ℕ) (A B WA WB : Finset ℕ), 0 < N → w ≤ N → M7.PrefixCompleted.Base N A B WA WB → ∀ E : Finset M5.BinaryPolynomial, M7.PrefixSector.ValidSector N E → M7.ScalarWork.sector N w E A B WA WB ≤ 1024 * N^4 * E.card * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N) := by
  classical
  intro N w A B WA WB hN hw hBase E hE
  change M7.ScalarWork.sector N w E A B WA WB ≤ _
  let C : ℕ := 1024 * N^4 * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N)
  calc
    M7.ScalarWork.sector N w E A B WA WB ≤ ∑ F ∈ E, C := by
      unfold M7.ScalarWork.sector
      apply Finset.sum_le_sum
      intro F hF
      exact M7.ScalarWork.prefix_bound N w A B WA WB hN hw hBase F
        (hE F hF).1 (hE F hF).2
    _ = E.card * C := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1024 * N^4 * E.card * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N) := by
      dsimp [C]
      ring
#print axioms M7.ScalarWork.mask_positions
#print axioms M7.ScalarWork.term_bound
#print axioms M7.ScalarWork.prefix_bound
#print axioms M7.ScalarWork.sector_bound

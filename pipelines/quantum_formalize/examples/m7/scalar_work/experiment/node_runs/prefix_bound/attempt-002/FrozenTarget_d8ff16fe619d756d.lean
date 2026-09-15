import M7ScalarWork

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (A B WA WB : Finset ℕ), 0 < N → w ≤ N → M7.PrefixCompleted.Base N A B WA WB → ∀ F : M5.BinaryPolynomial, F.Monic → F ∣ M5.cyclicModulus N → M7.ScalarWork.prefixWork N w F A B WA WB ≤ 1024 * N^4 * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N)

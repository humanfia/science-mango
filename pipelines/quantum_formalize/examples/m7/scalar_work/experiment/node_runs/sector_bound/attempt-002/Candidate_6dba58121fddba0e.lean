import FrozenTarget_6dba58121fddba0e
theorem M7.ScalarWork.sector_bound : QuantumHarnessFrozenTarget := by
  classical
  intro N w A B WA WB hN hw hBase E hE
  change M7.ScalarWork.sector N w E A B WA WB ≤ _
  let C : ℕ := 1024 * N^4 * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N)
  have hsum : M7.ScalarWork.sector N w E A B WA WB ≤ E.card * C := by
    unfold M7.ScalarWork.sector
    calc
      _ ≤ ∑ F ∈ E, C := by
        apply Finset.sum_le_sum
        intro F hF
        have hvalid := hE F hF
        exact M7.ScalarWork.prefix_bound N w A B WA WB hN hw hBase F hvalid.1 hvalid.2
      _ = E.card * C := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ E.card * C := hsum
    _ = 1024 * N^4 * E.card * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N) := by
      dsimp [C]
      ac_rfl

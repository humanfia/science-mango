import FrozenTarget_ec2103f718974bbf
theorem M7.ScalarWork.sector_bound : QuantumHarnessFrozenTarget := by
  classical
  intro N w A B WA WB hN hw hBase E hE
  change M7.ScalarWork.sector N w E A B WA WB ≤ _
  unfold M7.ScalarWork.sector
  calc
    _ ≤ ∑ F ∈ E, (1024 * N^4 * M7.ArithmeticLoops.divisorCount N *
        2^(M7.ArithmeticLoops.factorCount N + N)) := by
      apply Finset.sum_le_sum
      intro F hFE
      apply M7.ScalarWork.prefix_bound N w A B WA WB hN hw hBase F
      · unfold M7.PrefixSector.ValidSector at hE
        aesop
      · unfold M7.PrefixSector.ValidSector at hE
        aesop
    _ = 1024 * N^4 * E.card * M7.ArithmeticLoops.divisorCount N *
        2^(M7.ArithmeticLoops.factorCount N + N) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

import FrozenTarget_08885335eefdecac
theorem M6.Transfer.complete_address_capacity : QuantumHarnessFrozenTarget := by
  change ∀ R N slots : ℕ, R < N → slots ≤ 512*(N+1)^2 → M6.Transfer.solveStorage R N slots < 2^(M6.Transfer.actualAddressBits R N)
  intro R N slots hRN hslots
  have hexp : ∀ n : ℕ, n + 1 ≤ 2^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hN : N ≤ 2^N := by
    have := hexp N
    omega
  apply lt_of_le_of_lt (M6.Transfer.solve_storage_bound R N slots hRN hslots)
  change 16384*N^2*2^R < 2^(R+4*N+16)
  calc
    16384*N^2*2^R ≤ 16384*(2^N)^2*2^R := by
      gcongr
    _ = 2^(14+N*2+R) := by
      simp only [pow_add, pow_mul]
      norm_num
    _ < 2^(R+4*N+16) := by
      gcongr <;> omega

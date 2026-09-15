import FrozenTarget_d9291e135cdcab1e
theorem M6.Euclid.dense_rank : QuantumHarnessFrozenTarget := by
  change ∀ (width : ℕ) (p : M6.Euclid.BP), M6.Euclid.rank p ≤ width → M6.Euclid.scanRank width p = M6.Euclid.rank p
  classical
  intro width
  induction width with
  | zero =>
      intro p hp
      have hr : M6.Euclid.rank p = 0 := Nat.eq_zero_of_le_zero hp
      simp [M6.Euclid.scanRank, hr]
  | succ width ih =>
      intro p hp
      by_cases hsmall : M6.Euclid.rank p ≤ width
      · have hc : p.coeff width = 0 := by
          by_cases hz : p = 0
          · simp [hz]
          · have hd : p.natDegree < width := by
              simp [M6.Euclid.rank, hz] at hsmall
              omega
            exact Polynomial.coeff_eq_zero_of_natDegree_lt hd
        simpa [M6.Euclid.scanRank, List.range_succ, List.foldl_append, hc] using ih p hsmall
      · have hr : M6.Euclid.rank p = width + 1 := by omega
        have hz : p ≠ 0 := by
          intro hz
          simp [M6.Euclid.rank, hz] at hr
        have hd : p.natDegree = width := by
          simp [M6.Euclid.rank, hz] at hr
          omega
        have hc : p.coeff width ≠ 0 := by
          rw [← hd]
          exact Polynomial.coeff_natDegree_ne_zero.mpr hz
        simp [M6.Euclid.scanRank, List.range_succ, List.foldl_append, hc, hr]

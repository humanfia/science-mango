import FrozenTarget_a5909ac5f9c91d4e
theorem M6.Euclid.dense_injective : QuantumHarnessFrozenTarget := by
  intro N p q hp hq hd
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < N + 1
  · have hc : some (p.coeff i) = some (q.coeff i) := by
      simpa [M6.Euclid.dense, hi] using
        congrArg (fun l : List (ZMod 2) => l[i]?) hd
    exact Option.some.inj hc
  · have vanish : ∀ r : M6.Euclid.BP, M6.Euclid.rank r ≤ N + 1 → r.coeff i = 0 := by
      intro r hr
      by_cases hz : r = 0
      · simp [hz]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp [M6.Euclid.rank, hz] at hr
        omega
    rw [vanish p hp, vanish q hq]

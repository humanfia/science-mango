import FrozenTarget_a3f8f3cd251f0702
theorem M8.MixedNonproduct.mixed_obstruction : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN
  have hsmall : ∀ k : ℕ, 0 < k → k ≤ 3 → (k : ZMod N) ≠ 0 := by
    intro k hk hk3 he
    have hd : N ∣ k := (ZMod.natCast_zmod_eq_zero_iff_dvd k N).mp he
    have := Nat.le_of_dvd hk hd
    omega
  have h1 : (1 : ZMod N) ≠ 0 := hsmall 1 (by omega) (by omega)
  have h2 : (2 : ZMod N) ≠ 0 := hsmall 2 (by omega) (by omega)
  have h3 : (3 : ZMod N) ≠ 0 := hsmall 3 (by omega) (by omega)
  have hn12 : -(1 : ZMod N) ≠ 2 := by
    intro he
    apply h3
    linear_combination -he
  have hn21 : -(2 : ZMod N) ≠ 1 := by
    intro he
    apply h3
    linear_combination -he
  have hv : M6.Physical.conv N
      (M7.Supports.indicator (M8.MixedFamily.right N))
      (M7.Supports.indicator (M8.MixedFamily.left N)) 0 = 1 := by
    unfold M6.Physical.conv
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
    · intro j hj hj0
      by_cases hj1 : j = 1
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right,
          h1, h2, neg_ne_zero.mpr h1, hn12]
      by_cases hj2 : j = 2
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right,
          h1, h2, neg_ne_zero.mpr h2, hn21]
      simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right,
        hj0, hj1, hj2]
    · simp
  change M6.Physical.syndrome N
      (M7.Supports.indicator (M8.MixedFamily.left N))
      (M7.Supports.indicator (M8.MixedFamily.right N))
      (M7.Supports.indicator (M8.MixedFamily.left N),
        M7.Supports.indicator (M8.MixedFamily.right N)) = 0 ∧
    M6.Physical.syndrome N
      (M7.Supports.indicator (M8.MixedFamily.left N))
      (M7.Supports.indicator (M8.MixedFamily.right N)) (0, 0) = 0 ∧
    ¬ M6.Physical.syndrome N
      (M7.Supports.indicator (M8.MixedFamily.left N))
      (M7.Supports.indicator (M8.MixedFamily.right N))
      (M7.Supports.indicator (M8.MixedFamily.left N), 0) = 0
  constructor
  · simp only [M6.Physical.syndrome, Prod.fst, Prod.snd]
    rw [M6.Physical.conv_comm]
    ext i
    norm_num [← two_mul]
  constructor
  · ext i
    simp [M6.Physical.syndrome, M6.Physical.conv]
  · intro he
    have hz : M6.Physical.conv N
        (M7.Supports.indicator (M8.MixedFamily.left N)) 0 = 0 := by
      ext i
      simp [M6.Physical.conv]
    simp only [M6.Physical.syndrome, Prod.fst, Prod.snd, hz, add_zero, zero_add] at he
    have he0 := congrFun he 0
    rw [hv] at he0
    exact one_ne_zero he0

import FrozenTarget_2152ca52087cc5c9
theorem M8.MixedNonproduct.mixed_obstruction : QuantumHarnessFrozenTarget := by
    classical
    unfold QuantumHarnessFrozenTarget
    intro N inst hN
    have hsmall (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) : (k : ZMod N) ≠ 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd hk hd
      omega
    have h1 : (1 : ZMod N) ≠ 0 := by simpa using hsmall 1 (by omega) (by omega)
    have h2 : (2 : ZMod N) ≠ 0 := by simpa using hsmall 2 (by omega) (by omega)
    have h3 : (3 : ZMod N) ≠ 0 := by simpa using hsmall 3 (by omega) (by omega)
    have hn12 : (-1 : ZMod N) ≠ 2 := by
      intro h
      apply h3
      linear_combination h
    have hn21 : (-2 : ZMod N) ≠ 1 := by
      intro h
      apply h3
      linear_combination h
    have hp (j : ZMod N) (hj : j ≠ 0) :
        M7.Supports.indicator (M8.MixedFamily.left N) j *
          M7.Supports.indicator (M8.MixedFamily.right N) (-j) = 0 := by
      by_cases hj1 : j = 1
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.right, neg_ne_zero.mpr h1, hn12]
      · simp [M7.Supports.indicator, M8.MixedFamily.left, hj, hj1]
    have hq (j : ZMod N) (hj : j ≠ 0) :
        M7.Supports.indicator (M8.MixedFamily.right N) j *
          M7.Supports.indicator (M8.MixedFamily.left N) (-j) = 0 := by
      by_cases hj2 : j = 2
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.left, neg_ne_zero.mpr h2, hn21]
      · simp [M7.Supports.indicator, M8.MixedFamily.right, hj, hj2]
    have hs : (∑ j : ZMod N,
        M7.Supports.indicator (M8.MixedFamily.left N) j *
          M7.Supports.indicator (M8.MixedFamily.right N) (-j)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
      · intro j _ hj
        exact hp j hj
      · simp
    have ht : (∑ j : ZMod N,
        M7.Supports.indicator (M8.MixedFamily.right N) j *
          M7.Supports.indicator (M8.MixedFamily.left N) (-j)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
      · intro j _ hj
        exact hq j hj
      · simp
    refine ⟨?_, ?_, ?_⟩
    · change M6.Physical.syndrome N
          (M7.Supports.indicator (M8.MixedFamily.left N))
          (M7.Supports.indicator (M8.MixedFamily.right N))
          (M7.Supports.indicator (M8.MixedFamily.left N),
           M7.Supports.indicator (M8.MixedFamily.right N)) = 0
      unfold M6.Physical.syndrome
      rw [M6.Physical.conv_comm]
      ext i
      simp [← two_mul]
    · change M6.Physical.syndrome N
          (M7.Supports.indicator (M8.MixedFamily.left N))
          (M7.Supports.indicator (M8.MixedFamily.right N)) (0, 0) = 0
      ext i
      simp [M6.Physical.syndrome, M6.Physical.conv]
    · intro hz
      change M6.Physical.syndrome N
          (M7.Supports.indicator (M8.MixedFamily.left N))
          (M7.Supports.indicator (M8.MixedFamily.right N))
          (M7.Supports.indicator (M8.MixedFamily.left N), 0) = 0 at hz
      have he := congrFun hz (0 : ZMod N)
      have hf : (1 : ZMod 2) = 0 := by
        simpa [M6.Physical.syndrome, M6.Physical.conv, hs, ht] using he
      exact one_ne_zero hf

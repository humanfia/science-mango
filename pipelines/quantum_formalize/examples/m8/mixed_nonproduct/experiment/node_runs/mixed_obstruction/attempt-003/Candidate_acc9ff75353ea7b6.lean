import FrozenTarget_acc9ff75353ea7b6
theorem M8.MixedNonproduct.mixed_obstruction : QuantumHarnessFrozenTarget := by
    classical
    intro N inst hN
    have hsmall (k : ℕ) (hk : 0 < k) (hk' : k ≤ 4) : (k : ZMod N) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      have hkN : k < N := by omega
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt hkN] at hv
      omega
    have h1 : (1 : ZMod N) ≠ 0 := by simpa using hsmall 1 (by omega) (by omega)
    have h2 : (2 : ZMod N) ≠ 0 := by simpa using hsmall 2 (by omega) (by omega)
    have h3 : (3 : ZMod N) ≠ 0 := by simpa using hsmall 3 (by omega) (by omega)
    have hn12 : (-1 : ZMod N) ≠ 2 := by
      intro h
      have he := congrArg (fun x : ZMod N => x + 1) h
      norm_num at he
      exact h3 he.symm
    have hn21 : (-2 : ZMod N) ≠ 1 := by
      intro h
      have he := congrArg (fun x : ZMod N => x + 2) h
      norm_num at he
      exact h3 he.symm
    have hp : ∀ j : ZMod N, j ≠ 0 →
        M7.Supports.indicator (M8.MixedFamily.left N) j *
          M7.Supports.indicator (M8.MixedFamily.right N) (-j) = 0 := by
      intro j hj
      by_cases hj1 : j = 1
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right, hn12, h1]
      · simp [M7.Supports.indicator, M8.MixedFamily.left, hj, hj1]
    have hq : ∀ j : ZMod N, j ≠ 0 →
        M7.Supports.indicator (M8.MixedFamily.right N) j *
          M7.Supports.indicator (M8.MixedFamily.left N) (-j) = 0 := by
      intro j hj
      by_cases hj2 : j = 2
      · subst j
        simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right, hn21, h2]
      · simp [M7.Supports.indicator, M8.MixedFamily.right, hj, hj2]
    have hs : (∑ j : ZMod N, M7.Supports.indicator (M8.MixedFamily.left N) j *
        M7.Supports.indicator (M8.MixedFamily.right N) (-j)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp [M7.Supports.indicator, M8.MixedFamily.left, M8.MixedFamily.right]
      · intro j _ hj
        exact hp j hj
      · simp
    have ht : (∑ j : ZMod N, M7.Supports.indicator (M8.MixedFamily.right N) j *
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
      rw [M6.Physical.conv_comm N (M7.Supports.indicator (M8.MixedFamily.left N))
        (M7.Supports.indicator (M8.MixedFamily.right N))]
      ext i
      have hc : ∀ x : ZMod 2, x + x = 0 := by decide
      exact hc _
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
      have he := congrArg (fun f => f 0) hz
      simpa [M6.Physical.syndrome, M6.Physical.conv, hs, ht] using he

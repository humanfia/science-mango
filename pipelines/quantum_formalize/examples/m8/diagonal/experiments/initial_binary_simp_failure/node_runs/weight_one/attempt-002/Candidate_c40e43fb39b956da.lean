import FrozenTarget_c40e43fb39b956da
theorem M8.Diagonal.weight_one : QuantumHarnessFrozenTarget := by
    classical
    intro N inst a
    have binary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
      intro x
      fin_cases x <;> simp
    constructor
    · intro h
      change (Finset.univ.filter (fun i => a i ≠ 0)).card = 1 at h
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
      have hs : ∀ i : ZMod N, a i ≠ 0 ↔ i = j := by
        intro i
        have hm := congrArg (fun s : Finset (ZMod N) => i ∈ s) hj
        simpa using hm
      refine ⟨j, ?_⟩
      funext i
      by_cases hi : i = j
      · subst i
        have haj : a j = 1 := binary (a j) ((hs j).2 rfl)
        simpa [M6.Physical.delta] using haj
      · have hai : a i = 0 := by
          by_contra hn
          exact hi ((hs i).1 hn)
        simp [M6.Physical.delta, hi, hai]
    · rintro ⟨j, rfl⟩
      change (Finset.univ.filter (fun i => M6.Physical.delta N j i ≠ 0)).card = 1
      apply Finset.card_eq_one.mpr
      refine ⟨j, ?_⟩
      ext i
      by_cases hi : i = j
      · subst i
        simp [M6.Physical.delta]
      · simp [M6.Physical.delta, hi]

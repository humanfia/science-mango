import FrozenTarget_ee467712c6aff331
theorem M8.Diagonal.weight_one : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a
  have binary_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x
    fin_cases x <;> simp
  constructor
  · intro h
    change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 1 at h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    have support : ∀ i : ZMod N, a i ≠ 0 ↔ i = j := by
      intro i
      have hi := Finset.ext_iff.mp hj i
      simpa using hi
    refine ⟨j, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i
      have hval := binary_one (a j) ((support j).2 rfl)
      simp [M6.Physical.delta, hval]
    · have hzero : a i = 0 := by
        by_contra hn
        exact hij ((support i).1 hn)
      simp [M6.Physical.delta, hij, Ne.symm hij, hzero]
  · rintro ⟨j, rfl⟩
    change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
    have hs : Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [M6.Physical.delta]
      · simp [M6.Physical.delta, hij, Ne.symm hij]
    rw [hs]
    simp

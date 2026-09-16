import FrozenTarget_44eb78e1feeb5aa6
theorem M8.Diagonal.weight_one : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a
  have binary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x hx
    fin_cases x <;> norm_num at *
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
    by_cases hi : i = j
    · subst i
      have ha : a j = 1 := binary (a j) ((support j).mpr rfl)
      simp [M6.Physical.delta, ha]
    · have ha : a i = 0 := by
        by_contra hn
        exact hi ((support i).mp hn)
      simp [M6.Physical.delta, hi, Ne.symm hi, ha]
  · rintro ⟨j, rfl⟩
    simp [M6.Physical.weight, M6.Physical.delta]

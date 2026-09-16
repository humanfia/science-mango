import FrozenTarget_e3c7779986b23ad5
theorem M8.Diagonal.weight_one : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 1 ↔ ∃ j : ZMod N, a = M6.Physical.delta N j
  intro N _ a
  classical
  have binary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x
    fin_cases x <;> simp
  constructor
  · intro h
    change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 1 at h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    have hs : ∀ i : ZMod N, a i ≠ 0 ↔ i = j := by
      intro i
      have hi := congrArg (fun s : Finset (ZMod N) => i ∈ s) hj
      simpa using hi
    refine ⟨j, ?_⟩
    funext i
    by_cases hi : i = j
    · have hai : a i = 1 := binary (a i) ((hs i).mpr hi)
      simp [M6.Physical.delta, hi, hai]
    · have hai : a i = 0 := by
        by_contra hn
        exact hi ((hs i).mp hn)
      simp [M6.Physical.delta, hi, Ne.symm hi, hai]
  · rintro ⟨j, rfl⟩
    change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext i
    by_cases hi : i = j
    · simp [M6.Physical.delta, hi]
    · simp [M6.Physical.delta, hi, Ne.symm hi]

import FrozenTarget_f0bc6f02a55d68b8
theorem M8.Diagonal.weight_one : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ a : M6.Physical.Block N, M6.Physical.weight N a = 1 ↔ ∃ j : ZMod N, a = M6.Physical.delta N j
  intro N inst a
  classical
  have bit_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
    intro x
    fin_cases x
    · intro hx
      exact (hx rfl).elim
    · intro _
      rfl
  constructor
  · intro h
    change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 1 at h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
    have hs : ∀ i : ZMod N, a i ≠ 0 ↔ i = j := by
      intro i
      have hm := congrArg (fun s : Finset (ZMod N) => i ∈ s) hj
      simpa using hm
    refine ⟨j, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i
      have hone : a j = 1 := bit_one (a j) ((hs j).mpr rfl)
      simpa [M6.Physical.delta] using hone
    · have hzero : a i = 0 := by
        by_contra hn
        exact hij ((hs i).mp hn)
      simp [M6.Physical.delta, hij, hzero]
  · rintro ⟨j, rfl⟩
    change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
    apply Finset.card_eq_one.mpr
    refine ⟨j, ?_⟩
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij]

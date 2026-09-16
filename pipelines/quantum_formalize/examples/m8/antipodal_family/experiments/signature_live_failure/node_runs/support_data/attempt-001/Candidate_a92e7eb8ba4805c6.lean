import FrozenTarget_a92e7eb8ba4805c6
theorem M8.AntipodalFamily.support_data : QuantumHarnessFrozenTarget := by
    classical
    intro N inst hN hEven
    have hh : 4 ≤ N / 2 := by omega
    have hs : N / 2 + 1 < N := by omega
    have hne : ∀ a b : ℕ, a < N → b < N → a ≠ b → (a : ZMod N) ≠ (b : ZMod N) := by
      intro a b ha hb hab he
      have hv := congrArg (fun x : ZMod N => x.val) he
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hb] at hv
      exact hab hv
    have h01 : (0 : ZMod N) ≠ 1 := by
      simpa only [Nat.cast_zero, Nat.cast_one] using hne 0 1 (by omega) (by omega) (by omega)
    have h0h : (0 : ZMod N) ≠ (N / 2 : ℕ) := by
      simpa only [Nat.cast_zero] using hne 0 (N / 2) (by omega) (by omega) (by omega)
    have h0s : (0 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
      simpa only [Nat.cast_zero] using hne 0 (N / 2 + 1) (by omega) hs (by omega)
    have h1h : (1 : ZMod N) ≠ (N / 2 : ℕ) := by
      simpa only [Nat.cast_one] using hne 1 (N / 2) (by omega) (by omega) (by omega)
    have h1s : (1 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
      simpa only [Nat.cast_one] using hne 1 (N / 2 + 1) (by omega) hs (by omega)
    have hhs : ((N / 2 : ℕ) : ZMod N) ≠ (N / 2 + 1 : ℕ) :=
      hne (N / 2) (N / 2 + 1) (by omega) hs (by omega)
    constructor
    · simp only [M8.AntipodalFamily.support, Finset.card_insert_of_notMem,
        Finset.mem_insert, Finset.mem_singleton, h01, h0h, h0s, h1h, h1s,
        hhs, or_self, not_false_eq_true, Finset.card_singleton] <;> norm_num
    · simp [M8.AntipodalFamily.support]

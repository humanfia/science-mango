import FrozenTarget_a99443513ba478ce
theorem M8.AntipodalFamily.support_data : QuantumHarnessFrozenTarget := by
    classical
    intro N inst hN hEven
    have hh : 4 ≤ N / 2 := by omega
    have hs : N / 2 + 1 < N := by omega
    have hne : ∀ a b : ℕ, a < N → b < N → a ≠ b →
        (a : ZMod N) ≠ (b : ZMod N) := by
      intro a b ha hb hab heq
      have hv := congrArg (fun z : ZMod N => z.val) heq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
      exact hab hv
    have h01 := hne 0 1 (by omega) (by omega) (by omega)
    have h0h := hne 0 (N / 2) (by omega) (by omega) (by omega)
    have h0s := hne 0 (N / 2 + 1) (by omega) hs (by omega)
    have h1h := hne 1 (N / 2) (by omega) (by omega) (by omega)
    have h1s := hne 1 (N / 2 + 1) (by omega) hs (by omega)
    have hhs := hne (N / 2) (N / 2 + 1) (by omega) hs (by omega)
    simp only [Nat.cast_zero, Nat.cast_one] at h01 h0h h0s h1h h1s
    simp [M8.AntipodalFamily.support, h01, h0h, h0s, h1h, h1s, hhs]

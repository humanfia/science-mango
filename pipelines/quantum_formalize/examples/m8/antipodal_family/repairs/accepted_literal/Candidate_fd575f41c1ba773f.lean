import FrozenTarget_fd575f41c1ba773f
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  have hhalf : 1 < N / 2 := by omega
  have hlt : N / 2 + 1 < N := by omega
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have v0 : (0 : ZMod N).val = 0 := by simp
  have v1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 (by omega)
  have vh : ((N / 2 : ℕ) : ZMod N).val = N / 2 := hv _ (by omega)
  have vs : ((N / 2 + 1 : ℕ) : ZMod N).val = N / 2 + 1 := hv _ hlt
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, v1] at hh
    omega
  have h0h : (0 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vh] at hh
    omega
  have h0s : (0 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vs] at hh
    omega
  have h1h : (1 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vh] at hh
    omega
  have h1s : (1 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vs] at hh
    omega
  have hhs : ((N / 2 : ℕ) : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [vh, vs] at hh
    omega
  have hn0 : N / 2 ≠ 0 := by omega
  have hn1 : N / 2 ≠ 1 := by omega
  have hs0 : N / 2 + 1 ≠ 0 := by omega
  have hs1 : N / 2 + 1 ≠ 1 := by omega
  simp only [M7.Supports.polynomial, M8.AntipodalFamily.support,
    Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h01, h0h, h0s, h1h, h1s, hhs, or_self, not_false_eq_true,
    Finset.sum_singleton]
  rw [v0, v1, vh, vs]
  simp only [pow_zero, pow_one, M8.AntipodalFamily.polynomial, pow_succ]
  ring

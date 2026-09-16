import FrozenTarget_2c4f7049c9fcb349
theorem M8.P3Family.support_data : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → (M8.P3Family.support N).card = 3 ∧ (0 : ZMod N) ∈ M8.P3Family.support N ∧ (1 : ZMod N) ∈ M8.P3Family.support N
  intro N inst hN
  classical
  have hinj (a b : ℕ) (ha : a < N) (hb : b < N) (h : (a : ZMod N) = (b : ZMod N)) : a = b := by
    have hv := congrArg (fun x : ZMod N => x.val) h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := hinj 0 1 (by omega) (by omega) (by simpa using h)
    omega
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have hh := hinj 0 2 (by omega) (by omega) (by simpa using h)
    omega
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have hh := hinj 1 2 (by omega) (by omega) (by simpa using h)
    omega
  simp [M8.P3Family.support, h01, h02, h12]

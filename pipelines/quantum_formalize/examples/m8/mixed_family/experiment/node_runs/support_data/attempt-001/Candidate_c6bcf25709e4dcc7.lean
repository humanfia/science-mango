import FrozenTarget_c6bcf25709e4dcc7
theorem M8.MixedFamily.support_data : QuantumHarnessFrozenTarget := by
  intro N inst hN
  have hsmall : ∀ k : ℕ, 0 < k → k < N → (k : ZMod N) ≠ 0 := by
    intro k hk hkN he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hkN] at hv
    omega
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using Ne.symm (hsmall 1 (by omega) (by omega))
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using Ne.symm (hsmall 2 (by omega) (by omega))
  simp [M8.MixedFamily.left, M8.MixedFamily.right, h01, h02]

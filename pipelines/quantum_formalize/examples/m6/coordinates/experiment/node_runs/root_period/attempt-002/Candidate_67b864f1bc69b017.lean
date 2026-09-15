import FrozenTarget_67b864f1bc69b017
theorem M6.Coordinates.root_period : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N)) ^ N = 1
  intro N hN
  have h := AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  change Polynomial.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (AdjoinRoot.root (M6.Cyclic.modulus N)) (Polynomial.X ^ N + 1) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one] at h
  have h₂ : (1 : ZMod 2) + 1 = 0 := by decide
  have h₂' : (1 : AdjoinRoot (M6.Cyclic.modulus N)) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.of (M6.Cyclic.modulus N)) h₂
  exact add_right_cancel (h.trans h₂'.symm)

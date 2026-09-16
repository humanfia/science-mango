import FrozenTarget_f0b0691227c5bf01
theorem M8.P4Gcd.cofactor_coprime : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, IsCoprime (Polynomial.X + 1) (M8.P4Gcd.oddCofactor m)
  intro m
  have hneg : -(1 : Polynomial (ZMod 2)) = 1 := by
    have h : -(1 : ZMod 2) = 1 := by decide
    simpa using congrArg Polynomial.C h
  have hd : Polynomial.X - Polynomial.C (1 : ZMod 2) ∣
      M8.P4Gcd.oddCofactor m - 1 := by
    first
    | apply Polynomial.dvd_iff_isRoot.mpr
    | apply Polynomial.X_sub_C_dvd_iff.mpr
    change Polynomial.eval 1 (M8.P4Gcd.oddCofactor m - 1) = 0
    simp [M8.P4Gcd.cofactor_eval]
  have hd' : Polynomial.X + 1 ∣ M8.P4Gcd.oddCofactor m - 1 := by
    simpa only [Polynomial.C_1, sub_eq_add_neg, hneg] using hd
  obtain ⟨q, hq⟩ := hd'
  refine ⟨-q, 1, ?_⟩
  linear_combination hq

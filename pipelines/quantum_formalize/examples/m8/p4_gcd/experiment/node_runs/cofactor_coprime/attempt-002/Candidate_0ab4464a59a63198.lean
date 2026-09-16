import FrozenTarget_0ab4464a59a63198
theorem M8.P4Gcd.cofactor_coprime : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, IsCoprime (Polynomial.X + 1) (M8.P4Gcd.oddCofactor m)
  intro m
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hr : Polynomial.IsRoot (M8.P4Gcd.oddCofactor m - 1) (-1 : ZMod 2) := by
    change Polynomial.eval (-1) (M8.P4Gcd.oddCofactor m - 1) = 0
    rw [hneg]
    simp [M8.P4Gcd.cofactor_eval]
  have hd : Polynomial.X + 1 ∣ M8.P4Gcd.oddCofactor m - 1 := by
    simpa only [map_neg, map_one, sub_neg_eq_add] using
      (Polynomial.dvd_iff_isRoot.mpr hr)
  rcases hd with ⟨q, hq⟩
  refine ⟨-q, 1, ?_⟩
  calc
    -q * (Polynomial.X + 1) + 1 * M8.P4Gcd.oddCofactor m =
        M8.P4Gcd.oddCofactor m - (Polynomial.X + 1) * q := by ring
    _ = 1 := by rw [← hq]; ring

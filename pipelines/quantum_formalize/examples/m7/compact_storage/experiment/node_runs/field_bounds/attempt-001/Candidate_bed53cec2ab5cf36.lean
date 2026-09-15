import FrozenTarget_bed53cec2ab5cf36
theorem M7.CompactStorage.field_bounds : QuantumHarnessFrozenTarget := by
    change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), _
    intro N inst c
    classical
    constructor
    · have hd := (M7.RecipeSignature.signature_properties N c).2
      have hn := (M7.SignatureTau.modulus_monic N).ne_zero
      refine (Polynomial.natDegree_le_of_dvd hd hn).trans ?_
      change (Polynomial.X ^ N + 1 : M6.Cyclic.BinaryPolynomial).natDegree ≤ N
      simpa using (Polynomial.natDegree_add_le
        (Polynomial.X ^ N : M6.Cyclic.BinaryPolynomial) 1)
    · have hcard : M7.ActualOrbit.stabilizerCount c ≤ Fintype.card (M7.Action.Record N) := by
        change (M7.ActualOrbit.fullStabilizer c).card ≤ Fintype.card (M7.Action.Record N)
        exact Finset.card_le_univ _
      have hb : Fintype.card (M7.Action.Record N) ≤ 2 * N ^ 3 := by
        calc
          Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N := M7.Action.record_card N
          _ ≤ N * 2 * N * N := by
            gcongr <;> exact Nat.totient_le N
          _ = 2 * N ^ 3 := by ring
      have hp : ∀ n : ℕ, n < 2 ^ n := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
            rw [pow_succ]
            have hpos : 0 < (2 : ℕ) ^ n := by positivity
            omega
      have hc : N ^ 3 < (2 ^ N) ^ 3 := by
        have h := hp N
        gcongr
      calc
        M7.ActualOrbit.stabilizerCount c ≤ 2 * N ^ 3 := hcard.trans hb
        _ < 2 * (2 ^ N) ^ 3 := by omega
        _ = 2 ^ (1 + 3 * N) := by
          simp [← pow_mul, pow_add, Nat.mul_comm]

import FrozenTarget_51411acd308f2a88
theorem M6.ActualCounts.input_normalization : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b ha hb
  have hs := M6.ActualCounts.dual_weighted_sum N a b ha hb
    (fun _ => (1 : Polynomial ℤ))
  have hc : (Fintype.card (M6.Physical.Block N) : ℤ) =
      (2 : ℤ) ^ M6.ActualCounts.f N a b *
        (M6.Character.subspaceWords (M6.Spaces.D N
          (M6.Coordinates.coefficients N a)
          (M6.Coordinates.coefficients N b))).card := by
    simpa [Polynomial.coeff_sum, Polynomial.coeff_C_mul] using
      congrArg (fun p : Polynomial ℤ => p.coeff 0) hs
  have hn : Fintype.card (M6.Physical.Block N) =
      2 ^ M6.ActualCounts.f N a b *
        (M6.Character.subspaceWords (M6.Spaces.D N
          (M6.Coordinates.coefficients N a)
          (M6.Coordinates.coefficients N b))).card := by
    exact_mod_cast hc
  rw [← hn]
  simpa only [Nat.card_eq_fintype_card] using M6.Spaces.input_card N

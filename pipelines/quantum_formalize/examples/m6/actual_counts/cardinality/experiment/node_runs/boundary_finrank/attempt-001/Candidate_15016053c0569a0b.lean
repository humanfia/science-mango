import FrozenTarget_15016053c0569a0b
theorem M6.ActualCounts.boundary_finrank : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  classical
  let S := M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  let e : S ≃ {v // v ∈ M6.Character.subspaceWords S} :=
    { toFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      invFun := fun v => ⟨v.1, by simpa [M6.Character.subspaceWords] using v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card S = (M6.Character.subspaceWords S).card := by
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card]
  have hp : Nat.card S = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) S :=
    Module.natCard_eq_pow_finrank (K := ZMod 2)
  apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
  change (2 : ℕ) ^ Module.finrank (ZMod 2) S = 2 ^ (N - M6.ActualCounts.f N a b)
  calc
    (2 : ℕ) ^ Module.finrank (ZMod 2) S = Nat.card S := by
      simpa only [Nat.card_zmod] using hp.symm
    _ = (M6.Character.subspaceWords S).card := hc
    _ = 2 ^ (N - M6.ActualCounts.f N a b) := by
      simpa only [S, M6.Spaces.boundaryWords] using
        M6.ActualCounts.boundary_card N a b ha hb

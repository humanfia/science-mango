import FrozenTarget_037ff652cc15f58f
theorem M6.ActualCounts.dual_boundary_finrank : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb
  classical
  let S := M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
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
    _ = (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card :=
      M6.Spaces.dual_boundary_card N _ _
    _ = 2 ^ (N - M6.ActualCounts.f N a b) :=
      M6.ActualCounts.boundary_card N a b ha hb

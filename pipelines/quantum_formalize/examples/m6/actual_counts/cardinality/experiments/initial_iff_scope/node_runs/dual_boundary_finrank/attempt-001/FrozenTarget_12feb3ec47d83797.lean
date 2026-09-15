import M6ActualCardinality
import M6ActualCountsAccepted

theorem M6.ActualCounts.f_le_order : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), M6.ActualCounts.f N a b ≤ N := by
  intro N inst a b
  change (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree ≤ N
  have hm := M6.Coordinates.modulus_monic_degree N
  have hd := (M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N)).2.2
  simpa only [hm.2] using Polynomial.natDegree_le_of_dvd hd hm.1.ne_zero

theorem M6.ActualCounts.boundary_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N-(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  have h := M6.ActualCounts.input_normalization N a b ha hb
  rw [M6.Spaces.dual_boundary_card] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : M6.ActualCounts.f N a b + (N - M6.ActualCounts.f N a b) = N := by
    omega
  have hpow : (2 : ℕ)^N = 2^(M6.ActualCounts.f N a b) * 2^(N - M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow

theorem M6.ActualCounts.boundary_finrank : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b)

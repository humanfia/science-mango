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

theorem M6.ActualCounts.cycle_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N+(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  have h := M6.Character.dual_cardinality (2 * N)
    (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
  change (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))).card *
    (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(2 * N) at h
  rw [M6.Spaces.dual_boundary_card, M6.ActualCounts.boundary_card N a b ha hb] at h
  have hf := M6.ActualCounts.f_le_order N a b
  have hexp : (N - M6.ActualCounts.f N a b) + (N + M6.ActualCounts.f N a b) = 2 * N := by
    omega
  have hpow : (2 : ℕ)^(2 * N) = 2^(N - M6.ActualCounts.f N a b) * 2^(N + M6.ActualCounts.f N a b) := by
    rw [← pow_add, hexp]
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ)^(N - M6.ActualCounts.f N a b) by positivity)
  exact h.trans hpow

theorem M6.ActualCounts.dual_boundary_finrank : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b) := by
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

theorem M6.ActualCounts.logical_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ) = (2 : ℤ)^(N+(M6.ActualCounts.f N a b)) - (2 : ℤ)^(N-(M6.ActualCounts.f N a b)) := by
  intro N inst a b ha hb
  classical
  have hsub := M6.Spaces.boundaries_are_cycles N
    (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
  rw [M6.Spaces.logicalWords, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub),
    M6.ActualCounts.cycle_card N a b ha hb,
    M6.ActualCounts.boundary_card N a b ha hb]
  norm_cast

theorem M6.ActualCounts.encoded_dimension : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → 2 * N - Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) - Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = 2 * (M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  rw [M6.ActualCounts.boundary_finrank N a b ha hb,
    M6.ActualCounts.dual_boundary_finrank N a b ha hb]
  have hf := M6.ActualCounts.f_le_order N a b
  omega

theorem M6.ActualCounts.logicals_nonempty_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).Nonempty ↔ 0 < M6.ActualCounts.f N a b) := by
  intro N inst a b ha hb
  classical
  rw [← Finset.card_pos]
  have hc := M6.ActualCounts.logical_card N a b ha hb
  constructor
  · intro hpos
    by_contra h
    have hf0 : M6.ActualCounts.f N a b = 0 := by omega
    simp only [hf0, Nat.add_zero, Nat.sub_zero, sub_self] at hc
    have hpos' : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      exact_mod_cast hpos
    omega
  · intro hf
    have hexp : N - M6.ActualCounts.f N a b < N + M6.ActualCounts.f N a b := by omega
    have hp : (2 : ℤ) ^ (N - M6.ActualCounts.f N a b) < (2 : ℤ) ^ (N + M6.ActualCounts.f N a b) :=
      pow_lt_pow_right₀ (by norm_num) hexp
    have hpos : (0 : ℤ) < (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card := by
      rw [hc]
      exact sub_pos.mpr hp
    exact_mod_cast hpos

theorem M6.ActualCounts.zero_signature_no_logicals : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → M6.ActualCounts.f N a b = 0 → M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) = ∅ := by
  intro N inst a b ha hb hf
  apply Finset.card_eq_zero.mp
  have h := M6.ActualCounts.logical_card N a b ha hb
  simp only [hf, Nat.add_zero, Nat.sub_zero, sub_self] at h
  exact_mod_cast h
#print axioms M6.ActualCounts.f_le_order
#print axioms M6.ActualCounts.boundary_card
#print axioms M6.ActualCounts.boundary_finrank
#print axioms M6.ActualCounts.cycle_card
#print axioms M6.ActualCounts.dual_boundary_finrank
#print axioms M6.ActualCounts.encoded_dimension
#print axioms M6.ActualCounts.logical_card
#print axioms M6.ActualCounts.logicals_nonempty_iff
#print axioms M6.ActualCounts.zero_signature_no_logicals

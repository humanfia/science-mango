import M6TransferFactorBounds

theorem M6.Transfer.boundary_factor_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) ≤ 1 ∧ (M6.Character.boundaryFactor P i s).natDegree ≤ 1 := by
  classical
  intro m P i s
  by_cases h : P i = none ∨ P i = some s
  · simp only [M6.Character.boundaryFactor, if_pos h]
    constructor
    · have hx : (Polynomial.X : Polynomial ℤ) ^ s.val = Polynomial.monomial s.val 1 := by
        ext n
        simp [Polynomial.coeff_monomial, eq_comm]
      rw [hx, M6.Transfer.mass_basic.2.2.1]
      norm_num
    · have hs := ZMod.val_lt s
      rw [Polynomial.natDegree_X_pow]
      omega
  · simp [M6.Character.boundaryFactor, h, M6.Transfer.mass_basic.1]

theorem M6.Transfer.boundary_edge_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i j : Fin m) (s t : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t) ≤ 4 ∧ (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t).natDegree ≤ 2 := by
  intro m P i j s t
  obtain ⟨hmi, hdi⟩ := M6.Transfer.boundary_factor_bounds m P i s
  obtain ⟨hmj, hdj⟩ := M6.Transfer.boundary_factor_bounds m P j t
  constructor
  · calc
      M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s * M6.Character.boundaryFactor P j t)
          ≤ M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) *
            M6.Transfer.polynomialMass (M6.Character.boundaryFactor P j t) :=
        M6.Transfer.mass_mul _ _
      _ ≤ 1 * 1 := Nat.mul_le_mul hmi hmj
      _ ≤ 4 := by norm_num
  · exact le_trans Polynomial.natDegree_mul_le (by omega)

theorem M6.Transfer.character_factor_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.pinnedCharacterFactor P i s) ≤ 2 ∧ (M6.Character.pinnedCharacterFactor P i s).natDegree ≤ 1 := by
  classical
  intro m P i s
  let f : ZMod 2 → Polynomial ℤ := fun t =>
    Polynomial.C (M6.Character.sign (s * t)) * M6.Character.boundaryFactor P i t
  have hm (t : ZMod 2) : M6.Transfer.polynomialMass (f t) ≤ 1 := by
    have hc : M6.Transfer.polynomialMass (Polynomial.C (M6.Character.sign (s * t))) = 1 := by
      simpa [M6.Character.sign] using
        (M6.Transfer.mass_basic.2.2.1 0 (M6.Character.sign (s * t)))
    have h := M6.Transfer.mass_mul
      (Polynomial.C (M6.Character.sign (s * t))) (M6.Character.boundaryFactor P i t)
    change M6.Transfer.polynomialMass (f t) ≤ _ at h
    rw [hc, one_mul] at h
    exact le_trans h (M6.Transfer.boundary_factor_bounds m P i t).1
  have hd (t : ZMod 2) : (f t).natDegree ≤ 1 := by
    have h : (f t).natDegree ≤ (M6.Character.boundaryFactor P i t).natDegree := by
      simpa [f] using
        (Polynomial.natDegree_mul_le
          (p := Polynomial.C (M6.Character.sign (s * t)))
          (q := M6.Character.boundaryFactor P i t))
    exact le_trans h (M6.Transfer.boundary_factor_bounds m P i t).2
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have he : M6.Character.pinnedCharacterFactor P i s = f 0 + f 1 := by
    change (∑ t : ZMod 2, f t) = f 0 + f 1
    rw [hu]
    simp
  rw [he]
  constructor
  · exact le_trans (M6.Transfer.mass_add (f 0) (f 1)) (by have h0 := hm 0; have h1 := hm 1; omega)
  · exact le_trans (Polynomial.natDegree_add_le (f 0) (f 1)) (max_le (hd 0) (hd 1))

theorem M6.Transfer.character_edge_bounds : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i j : Fin m) (s t : ZMod 2), M6.Transfer.polynomialMass (M6.Character.pinnedCharacterFactor P i s * M6.Character.pinnedCharacterFactor P j t) ≤ 4 ∧ (M6.Character.pinnedCharacterFactor P i s * M6.Character.pinnedCharacterFactor P j t).natDegree ≤ 2 := by
  intro m P i j s t
  have hi := M6.Transfer.character_factor_bounds m P i s
  have hj := M6.Transfer.character_factor_bounds m P j t
  constructor
  · exact le_trans
      (M6.Transfer.mass_mul
        (M6.Character.pinnedCharacterFactor P i s)
        (M6.Character.pinnedCharacterFactor P j t))
      (by simpa using Nat.mul_le_mul hi.1 hj.1)
  · exact le_trans
      (Polynomial.natDegree_mul_le
        (p := M6.Character.pinnedCharacterFactor P i s)
        (q := M6.Character.pinnedCharacterFactor P j t))
      (by simpa using Nat.add_le_add hi.2 hj.2)
#print axioms M6.Transfer.boundary_factor_bounds
#print axioms M6.Transfer.boundary_edge_bounds
#print axioms M6.Transfer.character_factor_bounds
#print axioms M6.Transfer.character_edge_bounds

import FrozenTarget_f3467b701b8440ba
theorem M6.Transfer.character_factor_bounds : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.pinnedCharacterFactor P i s) ≤ 2 ∧ (M6.Character.pinnedCharacterFactor P i s).natDegree ≤ 1
  intro m P i s
  let f : ZMod 2 → Polynomial ℤ := fun t => Polynomial.C (M6.Character.sign (s * t)) * M6.Character.boundaryFactor P i t
  have hc (t : ZMod 2) : M6.Transfer.polynomialMass (Polynomial.C (M6.Character.sign (s * t))) = 1 := by
    have h := M6.Transfer.mass_basic.2.2.1 0 (M6.Character.sign (s * t))
    simpa [M6.Character.sign, Int.natAbs_pow] using h
  have hm (t : ZMod 2) : M6.Transfer.polynomialMass (f t) ≤ 1 := by
    have h := M6.Transfer.mass_mul (Polynomial.C (M6.Character.sign (s * t))) (M6.Character.boundaryFactor P i t)
    rw [hc t, one_mul] at h
    exact h.trans (M6.Transfer.boundary_factor_bounds m P i t).1
  have hd (t : ZMod 2) : (f t).natDegree ≤ 1 := by
    have h : (f t).natDegree ≤ (M6.Character.boundaryFactor P i t).natDegree := by
      simpa only [Polynomial.natDegree_C, zero_add] using (Polynomial.natDegree_mul_le (p := Polynomial.C (M6.Character.sign (s * t))) (q := M6.Character.boundaryFactor P i t))
    exact h.trans (M6.Transfer.boundary_factor_bounds m P i t).2
  change M6.Transfer.polynomialMass (∑ t, f t) ≤ 2 ∧ (∑ t, f t).natDegree ≤ 1
  constructor
  · calc
      M6.Transfer.polynomialMass (∑ t, f t) ≤ ∑ t, M6.Transfer.polynomialMass (f t) := M6.Transfer.mass_sum (ZMod 2) Finset.univ f
      _ ≤ ∑ _t : ZMod 2, (1 : ℕ) := Finset.sum_le_sum (fun t _ => hm t)
      _ = 2 := by norm_num
  · have hsum (u : Finset (ZMod 2)) : (∑ t ∈ u, f t).natDegree ≤ 1 := by
      induction u using Finset.induction_on with
      | empty => simp
      | @insert a u ha ih =>
        rw [Finset.sum_insert ha]
        exact Polynomial.natDegree_add_le.trans (max_le (hd a) ih)
    exact hsum Finset.univ

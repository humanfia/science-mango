import M7Domain

theorem M7.Domain.coefficients_indicator : ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.coefficients N (M7.Supports.polynomial A) = M7.Supports.indicator A := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.coefficients N (M7.Supports.polynomial A) = M7.Supports.indicator A
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst A
  funext i
  change (M7.Supports.polynomial A).coeff i.val = M7.Supports.indicator A i
  exact M7.Supports.indicator_coefficient N A i

theorem M7.Domain.shift_anchor : ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ q : ZMod N, q ∈ A → (0 : ZMod N) ∈ M7.Domain.shift A (-q) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ q : ZMod N, q ∈ A → (0 : ZMod N) ∈ M7.Domain.shift A (-q)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N _ A q hq
  classical
  unfold M7.Domain.shift
  apply Finset.mem_image.mpr
  exact ⟨q, hq, by simp⟩

theorem M7.Domain.shift_card : ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), ∀ r : ZMod N, (M7.Domain.shift A r).card = A.card := by
  intro N inst A r
  classical
  unfold M7.Domain.shift
  apply Finset.card_image_of_injective
  intro a b h
  simpa only [add_left_cancel_iff, add_right_cancel_iff] using h

theorem M7.Domain.support_gcd : ∀ (N : ℕ) [NeZero N] (A B : M7.Domain.Support N), Nat.gcd N (((M7.Supports.polynomial A).support ∪ (M7.Supports.polynomial B).support).gcd id) = M7.Domain.connectivityGcd A B := by
  intro N inst A B
  unfold M7.Domain.connectivityGcd
  rw [M7.Supports.support N A, M7.Supports.support N B]

theorem M7.Domain.admissible : ∀ (N w : ℕ) [NeZero N] (A B : M7.Domain.Support N), A.card = w → B.card = w → (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → M7.Domain.connectivityGcd A B = 1 → M6.Final.Admissible N (M7.Supports.polynomial A) (M7.Supports.polynomial B) := by
  intro N w inst A B hA hB h0A h0B hG
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have ha := (M7.Supports.anchor N A).2 h0A
  have hb := (M7.Supports.anchor N B).2 h0B
  have hcA := M7.Supports.support_card N A
  have hcB := M7.Supports.support_card N B
  have hdA := M7.Supports.degree_lt N A
  have hdB := M7.Supports.degree_lt N B
  have hg := (M7.Domain.support_gcd N A B).trans hG
  simp_all [M6.Final.Admissible, M6.ActualTransfer.span, max_lt_iff]

theorem M7.Domain.block_polynomial : ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.blockPolynomial N (M7.Supports.indicator A) = M7.Supports.polynomial A := by
  change ∀ (N : ℕ) [NeZero N] (A : M7.Domain.Support N), M6.Coordinates.blockPolynomial N (M7.Supports.indicator A) = M7.Supports.polynomial A
  intro N inst A
  classical
  apply Polynomial.ext
  intro n
  unfold M6.Coordinates.blockPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin N)]
    · simpa [Polynomial.coeff_C_mul_X_pow, ZMod.val_natCast, Nat.mod_eq_of_lt hn] using
        (M7.Supports.indicator_coefficient N A (n : ZMod N)).symm
    · intro j hj hne
      have hval : j.val ≠ n := by
        intro h
        apply hne
        exact Fin.ext h
      simp [Polynomial.coeff_C_mul_X_pow, hval, Ne.symm hval]
    · simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (M7.Supports.degree_lt N A) (Nat.le_of_not_gt hn))]
    apply Finset.sum_eq_zero
    intro j hj
    have hval : j.val ≠ n := by
      intro h
      exact hn (h ▸ j.isLt)
    simp [Polynomial.coeff_C_mul_X_pow, hval, Ne.symm hval]
#print axioms M7.Domain.coefficients_indicator
#print axioms M7.Domain.block_polynomial
#print axioms M7.Domain.shift_anchor
#print axioms M7.Domain.shift_card
#print axioms M7.Domain.support_gcd
#print axioms M7.Domain.admissible

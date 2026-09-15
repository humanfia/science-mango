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
#print axioms M7.Domain.coefficients_indicator
#print axioms M7.Domain.shift_anchor
#print axioms M7.Domain.shift_card
#print axioms M7.Domain.support_gcd

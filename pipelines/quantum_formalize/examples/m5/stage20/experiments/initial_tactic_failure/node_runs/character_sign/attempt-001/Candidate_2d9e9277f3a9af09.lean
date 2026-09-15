import FrozenTarget_2d9e9277f3a9af09
theorem M5.ArithmeticSubset.character_sign : QuantumHarnessFrozenTarget := by
  intro P hP lam z
  classical
  have hpow {R : Type*} [CommRing R] (n : ℕ) :
      (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rcases ih with h | h <;> simp [pow_succ, h]
  have hprod {R : Type*} [CommRing R] {ι : Type*}
      (s : Finset ι) (f : ι → ℕ) :
      (∏ i ∈ s, (-1 : R) ^ f i) = 1 ∨
        (∏ i ∈ s, (-1 : R) ^ f i) = -1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        rcases hpow (R := R) (f a) with h₁ | h₁ <;>
          rcases ih with h₂ | h₂ <;> simp [h₁, h₂]
  exact hprod _ _

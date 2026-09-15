import FrozenTarget_67144471d29e22ca
theorem M5.ArithmeticSubset.character_sign : QuantumHarnessFrozenTarget := by
  intro P hP lam z
  have hprod {R : Type} [CommRing R] {ι : Type}
      (s : Finset ι) (f : ι → ℕ) :
      (∏ i ∈ s, (-1 : R) ^ f i) = 1 ∨
        (∏ i ∈ s, (-1 : R) ^ f i) = -1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        rcases neg_one_pow_eq_or (R := R) (f a) with h | h <;>
          rcases ih with ih | ih <;> simp [h, ih]
  exact hprod _ _

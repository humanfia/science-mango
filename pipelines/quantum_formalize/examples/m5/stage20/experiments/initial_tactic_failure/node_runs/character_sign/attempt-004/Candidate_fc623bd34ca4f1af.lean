import FrozenTarget_fc623bd34ca4f1af
theorem M5.ArithmeticSubset.character_sign : QuantumHarnessFrozenTarget := by
  intro P hP lam z
  classical
  have hpow {R : Type*} [CommRing R] (n : ℕ) :
      (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]
  have hprod {R : Type*} [CommRing R] {ι : Type*}
      (s : Finset ι) (f : ι → ℕ) :
      (∏ i ∈ s, (-1 : R) ^ f i) = 1 ∨
        (∏ i ∈ s, (-1 : R) ^ f i) = -1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rcases hpow (R := R) (f a) with h | h <;>
        rcases ih with hs | hs <;>
        simp [Finset.prod_insert, ha, h, hs]
  exact hprod Finset.univ _

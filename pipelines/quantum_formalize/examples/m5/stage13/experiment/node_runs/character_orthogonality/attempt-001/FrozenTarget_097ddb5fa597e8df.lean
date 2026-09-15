import M5QuotientCharacter

theorem M5.QuotientCharacter.coordinates_zero_iff : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0 := by
  intro P hP z
  first
  | exact (M5.QuotientCharacter.coordinates P hP).map_eq_zero_iff
  | simp [M5.QuotientCharacter.coordinates]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z) = if z = 0 then (2 : ℤ) ^ P.natDegree else 0

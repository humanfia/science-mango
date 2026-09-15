import M5QuotientCharacter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (n : ℕ) (f : Fin n → AdjoinRoot P) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z * ∑ u : Fin n, M5.QuotientCharacter.value P hP lam (f u)) = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ)

import M5QuotientCharacter

#check (∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0)
#check (∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z u : AdjoinRoot P), M5.QuotientCharacter.value P hP lam (z + u) = M5.QuotientCharacter.value P hP lam z * M5.QuotientCharacter.value P hP lam u)
#check (∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z) = if z = 0 then (2 : ℤ) ^ P.natDegree else 0)
#check (∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (n : ℕ) (f : Fin n → AdjoinRoot P) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z * ∑ u : Fin n, M5.QuotientCharacter.value P hP lam (f u)) = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ))

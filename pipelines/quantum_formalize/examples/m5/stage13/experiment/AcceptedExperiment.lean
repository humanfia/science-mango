import M5QuotientCharacter

theorem M5.QuotientCharacter.character_add : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (lam : M5.Character.BinaryVector P.natDegree) (z u : AdjoinRoot P), M5.QuotientCharacter.value P hP lam (z + u) = M5.QuotientCharacter.value P hP lam z * M5.QuotientCharacter.value P hP lam u := by
  intro P hP lam z u
  unfold M5.QuotientCharacter.value
  simp only [map_add, M5.Character.character_add]

theorem M5.QuotientCharacter.coordinates_zero_iff : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), M5.QuotientCharacter.coordinates P hP z = 0 ↔ z = 0 := by
  intro P hP z
  first
  | exact (M5.QuotientCharacter.coordinates P hP).map_eq_zero_iff
  | simp [M5.QuotientCharacter.coordinates]

theorem M5.QuotientCharacter.finite_fibre_count : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (n : ℕ) (f : Fin n → AdjoinRoot P) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z * ∑ u : Fin n, M5.QuotientCharacter.value P hP lam (f u)) = (2 : ℤ) ^ P.natDegree * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ) := by
  classical
  intro P hP n f z
  have hfilter :
      (Finset.univ.filter (fun u : Fin n =>
        M5.QuotientCharacter.coordinates P hP (f u) =
          M5.QuotientCharacter.coordinates P hP z)) =
      (Finset.univ.filter (fun u : Fin n => f u = z)) := by
    apply Finset.filter_congr
    intro u hu
    exact (M5.QuotientCharacter.coordinates P hP).injective.eq_iff
  rw [← hfilter]
  unfold M5.QuotientCharacter.value
  apply M5.Character.finite_fibre_count

theorem M5.QuotientCharacter.character_orthogonality : ∀ (P : M5.BinaryPolynomial) (hP : P.Monic) (z : AdjoinRoot P), (∑ lam : M5.Character.BinaryVector P.natDegree, M5.QuotientCharacter.value P hP lam z) = if z = 0 then (2 : ℤ) ^ P.natDegree else 0 := by
  intro P hP z
  classical
  unfold M5.QuotientCharacter.value
  rw [M5.Character.character_orthogonality]
  simp only [M5.QuotientCharacter.coordinates_zero_iff]
#print axioms M5.QuotientCharacter.character_add
#print axioms M5.QuotientCharacter.coordinates_zero_iff
#print axioms M5.QuotientCharacter.character_orthogonality
#print axioms M5.QuotientCharacter.finite_fibre_count

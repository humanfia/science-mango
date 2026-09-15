import FrozenTarget_ccc5134a7b4d49c9
theorem M5.QuotientCharacter.finite_fibre_count : QuantumHarnessFrozenTarget := by
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

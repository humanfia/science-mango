import FrozenTarget_3a67eb82cd1cedac
theorem M5.ArithmeticTuple.numerator_exact : QuantumHarnessFrozenTarget := by
  intro P hP T d k z
  classical
  have hfilter :
      (Finset.univ.filter (fun t : Fin k → Fin (T / d) =>
        M5.TupleCharacter.vectorSum
          (fun j : Fin (T / d) => M5.QuotientCharacter.coordinates P hP
            (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) t =
          M5.QuotientCharacter.coordinates P hP z)) =
      (Finset.univ.filter (fun t : Fin k → Fin (T / d) =>
        AdjoinRoot.mk P (M5.ArithmeticTuple.tuplePolynomial T d k t) = z)) := by
    apply Finset.filter_congr
    intro t ht
    rw [← M5.ArithmeticTuple.tuple_coordinates P hP T d k t]
    exact (M5.QuotientCharacter.coordinates P hP).injective.eq_iff
  rw [← hfilter]
  simp only [M5.ArithmeticTuple.numerator, M5.QuotientCharacter.value]
  apply M5.TupleCharacter.ordered_tuple_power_count

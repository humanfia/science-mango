import FrozenTarget_100444e37183eb3e
theorem M5.AnchoredTupleCount.anchored_tuple_divisibility : QuantumHarnessFrozenTarget := by
  intro P T d k t
  have htwo : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    ext n
    by_cases h : n = 0 <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_one, h]
  have hquot : (1 : AdjoinRoot P) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.mk P) htwo
  rw [← AdjoinRoot.mk_eq_zero, map_add, map_one]
  constructor
  · intro h
    apply add_left_cancel (a := (1 : AdjoinRoot P))
    exact h.trans hquot.symm
  · intro h
    simpa only [h] using hquot

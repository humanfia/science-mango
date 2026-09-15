import FrozenTarget_37c1ba040d30e8ad
theorem M5.AnchoredTupleCount.anchored_tuple_divisibility : QuantumHarnessFrozenTarget := by
  intro P T d k t
  have hb : (1 : ZMod 2) + 1 = 0 := by decide
  have hp : (1 : M5.BinaryPolynomial) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) hb
  have htwo : (1 : AdjoinRoot P) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (AdjoinRoot.mk P) hp
  rw [← AdjoinRoot.mk_eq_zero, map_add, map_one]
  constructor
  · intro h
    exact add_left_cancel (h.trans htwo.symm)
  · intro h
    rw [h]
    exact htwo

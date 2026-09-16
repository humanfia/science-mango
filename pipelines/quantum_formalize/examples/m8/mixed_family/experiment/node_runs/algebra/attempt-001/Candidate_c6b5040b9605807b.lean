import FrozenTarget_c6b5040b9605807b
theorem M8.MixedFamily.algebra : QuantumHarnessFrozenTarget := by
  change (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) = (1 + Polynomial.X) ^ 2 ∧
    (1 + Polynomial.X : Polynomial (ZMod 2)) * (1 + Polynomial.X ^ 2) =
      1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3
  have h : (1 + 1 : Polynomial (ZMod 2)) = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (fun c : ZMod 2 => Polynomial.C c)
        (show (1 + 1 : ZMod 2) = 0 by decide)
  constructor
  · calc
      (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) =
          1 + Polynomial.X ^ 2 + (1 + 1) * Polynomial.X := by rw [h]; simp
      _ = (1 + Polynomial.X) ^ 2 := by ring
  · ring

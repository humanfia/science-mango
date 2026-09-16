import FrozenTarget_52a3ade3d1271225
theorem M8.MixedFamily.signature : QuantumHarnessFrozenTarget := by
  intro N inst hN
  have hp := M8.MixedFamily.literal_polynomials N hN
  have hab : M8.MixedFamily.a ∣ M8.MixedFamily.b := by
    rw [M8.MixedFamily.algebra.1]
    exact dvd_pow_self _ (by decide : 2 ≠ 0)
  have hn : -(1 : Polynomial (ZMod 2)) = 1 := by
    have h := congrArg (fun c : ZMod 2 => Polynomial.C c)
      (show -(1 : ZMod 2) = 1 by decide)
    simpa only [Polynomial.C_neg, Polynomial.C_1] using h
  have ham : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    simpa [M8.MixedFamily.a, M6.Cyclic.modulus, sub_eq_add_neg, hn, add_comm] using
      (sub_dvd_pow_sub_pow (Polynomial.X : Polynomial (ZMod 2)) 1 N)
  change EuclideanDomain.gcd
    (EuclideanDomain.gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
      (M7.Supports.polynomial (M8.MixedFamily.right N))) (M6.Cyclic.modulus N) = M8.MixedFamily.a
  rw [hp.1,hp.2,EuclideanDomain.gcd_eq_left.mpr hab]
  exact EuclideanDomain.gcd_eq_left.mpr ham

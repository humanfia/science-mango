import FrozenTarget_0edc1d96f8a8e5b0
theorem M8.P3Family.signature : QuantumHarnessFrozenTarget := by
  intro N inst hN hdiv
  have hl := M8.P3Family.literal_polynomial N hN
  have hd := M8.P3Family.divides_modulus N hdiv
  change EuclideanDomain.gcd
    (EuclideanDomain.gcd (M7.Supports.polynomial (M8.P3Family.support N))
      (M7.Supports.polynomial (M8.P3Family.support N))) (M6.Cyclic.modulus N) = M8.P3Family.polynomial
  rw [hl, EuclideanDomain.gcd_self]
  exact EuclideanDomain.gcd_eq_left.mpr hd

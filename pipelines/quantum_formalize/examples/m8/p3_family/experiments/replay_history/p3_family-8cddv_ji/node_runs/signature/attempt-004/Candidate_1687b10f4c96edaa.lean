import FrozenTarget_1687b10f4c96edaa
theorem M8.P3Family.signature : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M7.RecipeSignature.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial
  intro N inst hN hdiv
  classical
  have hl := M8.P3Family.literal_polynomial N hN
  have hd := M8.P3Family.divides_modulus N hdiv
  have hm : M8.P3Family.polynomial.Monic := by
    unfold M8.P3Family.polynomial
    monicity
  have hn := hm.normalize_eq_self
  have hg : gcd M8.P3Family.polynomial (M6.Cyclic.modulus N) = M8.P3Family.polynomial :=
    (gcd_eq_left_iff _ _ hn).2 hd
  first
  | change gcd (gcd (M7.Supports.polynomial (M8.P3Family.support N)) (M7.Supports.polynomial (M8.P3Family.support N))) (M6.Cyclic.modulus N) = _
  | change gcd (M7.Supports.polynomial (M8.P3Family.support N)) (gcd (M7.Supports.polynomial (M8.P3Family.support N)) (M6.Cyclic.modulus N)) = _
  | change normalize (gcd (gcd (M7.Supports.polynomial (M8.P3Family.support N)) (M7.Supports.polynomial (M8.P3Family.support N))) (M6.Cyclic.modulus N)) = _
  | change normalize (gcd (M7.Supports.polynomial (M8.P3Family.support N)) (gcd (M7.Supports.polynomial (M8.P3Family.support N)) (M6.Cyclic.modulus N))) = _
  simp only [hl, gcd_self, hn, hg]

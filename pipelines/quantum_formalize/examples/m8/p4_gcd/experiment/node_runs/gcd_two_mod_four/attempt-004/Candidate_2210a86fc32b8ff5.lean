import FrozenTarget_2210a86fc32b8ff5
theorem M8.P4Gcd.gcd_two_mod_four : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2
  intro m
  rw [M8.P4Family.power_identity, M8.P4Gcd.factorization]
  let p : M6.Cyclic.BinaryPolynomial := Polynomial.X + 1
  let H := M8.P4Gcd.oddCofactor m
  change gcd (p^3) (p^2 * H) = p^2
  have hm : p.Monic := by
    simpa only [p, Polynomial.C_1] using (Polynomial.monic_X_add_C (1 : ZMod 2))
  have hc : IsCoprime p H := M8.P4Gcd.cofactor_coprime m
  rcases hc with ⟨a, b, hab⟩
  let d := gcd (p^3) (p^2 * H)
  have hd₁ : d ∣ p^3 := gcd_dvd_left _ _
  have hd₂ : d ∣ p^2 * H := gcd_dvd_right _ _
  have hd : d ∣ p^2 := by
    rcases hd₁ with ⟨u, hu⟩
    rcases hd₂ with ⟨v, hv⟩
    refine ⟨a*u + b*v, ?_⟩
    calc
      p^2 = p^2 * (a*p + b*H) := by rw [hab, mul_one]
      _ = a*p^3 + b*(p^2*H) := by ring
      _ = d * (a*u + b*v) := by rw [hu, hv]; ring
  have hl : p^2 ∣ p^3 := by
    refine ⟨p, ?_⟩
    ring
  have hr : p^2 ∣ p^2 * H := ⟨H, rfl⟩
  exact (gcd_eq_normalize hd (dvd_gcd hl hr)).trans ((hm.pow 2).normalize_eq_self)

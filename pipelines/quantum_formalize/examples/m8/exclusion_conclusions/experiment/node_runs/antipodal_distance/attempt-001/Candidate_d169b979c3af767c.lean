import FrozenTarget_d169b979c3af767c
theorem M8.Exclusion.antipodal_distance : QuantumHarnessFrozenTarget := by
  intro N inst v hv hN
  have h8 : 8 ≤ N := by
    rw [hN]
    calc
      8 = (2 : ℕ)^3 := by norm_num
      _ ≤ 2^v := by gcongr <;> omega
  have heven : Even N := by
    have he : v = (v - 1) + 1 := by omega
    rw [hN, he, pow_succ]
    exact ⟨2^(v-1), by omega⟩
  have hp := M8.AntipodalFamily.literal_polynomial N h8 heven
  have hn := M8.AntipodalFamily.nontrivial N h8 heven
  have hd := M8.AntipodalFamily.degree_bound N h8 heven
  have hm : M8.AntipodalFamily.polynomial N ∣ M6.Cyclic.modulus N := by
    rw [hN]
    exact M8.AntipodalFamily.divides_modulus v hv
  change M6.Final.quantumDistance N
    (M7.Supports.polynomial (M8.AntipodalFamily.support N))
    (M7.Supports.polynomial (M8.AntipodalFamily.support N)) = some 2
  rw [hp]
  change M8.Diagonal.distance N
    (M6.Coordinates.coefficients N (M8.AntipodalFamily.polynomial N)) = some 2
  exact M8.DiagonalPolynomial.distance_two N
    (M8.AntipodalFamily.polynomial N) (M8.AntipodalFamily.polynomial N)
    hn.2.2.1 hd hn.1 hn.2.1 (dvd_refl _) hm

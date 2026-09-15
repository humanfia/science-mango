import M5Period

theorem M5.Period.cyclic_dvd_iff_root_pow : ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1 := by
  change ∀ (F : M5.BinaryPolynomial) (N : ℕ), F ∣ M5.cyclicModulus N ↔ (AdjoinRoot.root F) ^ N = 1
  intro F N
  have hpoly : -(1 : M5.BinaryPolynomial) = 1 := CharTwo.neg_eq _
  have hroot : -(1 : AdjoinRoot F) = 1 := by
    simpa only [map_neg, map_one] using congrArg (AdjoinRoot.mk F) hpoly
  rw [← AdjoinRoot.mk_eq_zero]
  simp [M5.cyclicModulus, map_add, map_pow, AdjoinRoot.mk_X,
    add_eq_zero_iff_eq_neg, hroot]

theorem M5.Period.quotient_finite : ∀ (F : M5.BinaryPolynomial), F.Monic → Finite (AdjoinRoot F) := by
  change ∀ (F : M5.BinaryPolynomial), F.Monic → Finite (AdjoinRoot F)
  intro F hF
  letI : Module.Finite (ZMod 2) (AdjoinRoot F) := hF.finite_adjoinRoot
  apply Module.finite_of_finite (ZMod 2)

theorem M5.Period.root_is_unit : ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F) := by
  change ∀ (F : M5.BinaryPolynomial), F.coeff 0 = 1 → IsUnit (AdjoinRoot.root F)
  intro F hF
  have h : AdjoinRoot.root F * AdjoinRoot.mk F F.divX + 1 = 0 := by
    simpa only [map_add, map_mul, hF, Polynomial.C_1, map_one,
      AdjoinRoot.mk_self, AdjoinRoot.root] using
      congrArg (AdjoinRoot.mk F) (Polynomial.X_mul_divX_add F)
  have hinv : AdjoinRoot.root F * (-AdjoinRoot.mk F F.divX) = 1 := by
    rw [mul_neg, eq_neg_of_add_eq_zero_left h, neg_neg]
  exact ⟨⟨AdjoinRoot.root F, -AdjoinRoot.mk F F.divX,
    hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩

theorem M5.Period.period_law : ∀ (F : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → 0 < M5.signaturePeriod F ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N := by
  change ∀ (F : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → 0 < M5.signaturePeriod F ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N
  intro F hmonic hcoeff
  letI : Finite (AdjoinRoot F) := M5.Period.quotient_finite F hmonic
  change 0 < orderOf (AdjoinRoot.root F) ∧ ∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ orderOf (AdjoinRoot.root F) ∣ N
  constructor
  · exact orderOf_pos_iff.mpr (M5.Period.root_is_unit F hcoeff).isOfFinOrder
  · intro N
    rw [M5.Period.cyclic_dvd_iff_root_pow, orderOf_dvd_iff_pow_eq_one]

theorem M5.Period.period_dvd_of_dvd : ∀ (F G : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → G.Monic → G.coeff 0 = 1 → F ∣ G → M5.signaturePeriod F ∣ M5.signaturePeriod G := by
  change ∀ (F G : M5.BinaryPolynomial), F.Monic → F.coeff 0 = 1 → G.Monic → G.coeff 0 = 1 → F ∣ G → M5.signaturePeriod F ∣ M5.signaturePeriod G
  intro F G hFm hFc hGm hGc hFG
  apply ((M5.Period.period_law F hFm hFc).2 (M5.signaturePeriod G)).mp
  apply dvd_trans hFG
  exact ((M5.Period.period_law G hGm hGc).2 (M5.signaturePeriod G)).mpr (dvd_refl _)

theorem M5.Period.period_one : M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1 := by
  change M5.signaturePeriod (1 : M5.BinaryPolynomial) = 1
  apply Nat.dvd_one.mp
  exact ((M5.Period.period_law (1 : M5.BinaryPolynomial)
    Polynomial.monic_one (by simp)).2 1).mp (one_dvd _)
#print axioms M5.Period.cyclic_dvd_iff_root_pow
#print axioms M5.Period.quotient_finite
#print axioms M5.Period.root_is_unit
#print axioms M5.Period.period_law
#print axioms M5.Period.period_dvd_of_dvd
#print axioms M5.Period.period_one

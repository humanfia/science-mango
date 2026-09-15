import M5OriginalSpec
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.PeriodClause F ∧ M5.Final.OrderClause w F ∧ M5.Final.LowerClause w F ∧ M5.Final.WeightOneClause F)
#check (M5.Final.NormalizationClause)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → F.Monic → F.coeff 0 = 1 → M5.Final.GlobalClause w F ∧ M5.Final.ProgressionClause w F ∧ M5.Final.BirthClause w F ∧ M5.Final.LaterClause w F)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Core w F)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OrderRecoveryClause w F)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.ResidueRecoveryClause w F)
#check (∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F)

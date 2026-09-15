import M5PeriodSearch
#check (∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → (M5.PeriodSearch.candidates F).Nonempty)
#check (∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F ∈ M5.PeriodSearch.candidates F)
#check (∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.PeriodSearch.finiteSearch F = M5.signaturePeriod F)
#check (M5.PeriodSearch.finiteSearch (1 : M5.BinaryPolynomial) = 1)

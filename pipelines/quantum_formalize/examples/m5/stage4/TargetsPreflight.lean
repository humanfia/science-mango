import M5Cardinality
#check (∀ F : M5.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree)
#check (∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree)
#print axioms M5.Period.quotient_finite

import M8DiagonalPolynomial
def target_0 : Prop := (∀ (N : ℕ) [NeZero N], M6.Coordinates.encode N (M6.Physical.delta N 0) = 1)
def target_1 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p F q : M8.DiagonalPolynomial.BP), F.Monic → F ∣ p → F ∣ M6.Cyclic.modulus N → M6.Cyclic.image N p * M6.Cyclic.image N q = 1 → F = 1)
def target_2 : Prop := (∀ (N : ℕ) [NeZero N], ∀ p : M8.DiagonalPolynomial.BP, p ≠ 0 → p.degree < (N : WithBot ℕ) → M6.Coordinates.coefficients N p ≠ 0)
def target_3 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p F : M8.DiagonalPolynomial.BP), p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ M6.Cyclic.modulus N → M8.Diagonal.DeltaNotImage N (M6.Coordinates.coefficients N p))
def target_4 : Prop := (∀ (N : ℕ) [NeZero N], ∀ (p F : M8.DiagonalPolynomial.BP), p ≠ 0 → p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ M6.Cyclic.modulus N → M8.Diagonal.distance N (M6.Coordinates.coefficients N p) = some 2)

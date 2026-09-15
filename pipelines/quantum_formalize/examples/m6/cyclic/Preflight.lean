import M6Cyclic
def check_0 : Prop := ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
def check_1 : Prop := ∀ a b M : M6.Cyclic.BinaryPolynomial, ∃ p q r : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M = p*a + q*b + r*M
def check_2 : Prop := ∀ a b M h : M6.Cyclic.BinaryPolynomial, (M ∣ a*h ∧ M ∣ b*h) ↔ M ∣ M6.Cyclic.signature a b M * h
def check_3 : Prop := ∀ F K h : M6.Cyclic.BinaryPolynomial, F ≠ 0 → (F*K ∣ F*h ↔ K ∣ h)
def check_4 : Prop := ∀ (N : ℕ) (a b : M6.Cyclic.BinaryPolynomial) (h : M6.Cyclic.CycleRing N), M6.Cyclic.syndrome N a b (M6.Cyclic.boundary N a b h) = 0
def check_5 : Prop := ∀ (N : ℕ) (a b h : M6.Cyclic.BinaryPolynomial), M6.Cyclic.boundary N a b (M6.Cyclic.image N h) = (0,0) ↔ M6.Cyclic.modulus N ∣ M6.Cyclic.signature a b (M6.Cyclic.modulus N) * h

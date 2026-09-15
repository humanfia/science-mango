import M6Coordinates
def check_0 : Prop := ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
def check_1 : Prop := ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N) (i : Fin N), (M6.Coordinates.blockPolynomial N h).coeff i.val = h (i.val : ZMod N)
def check_2 : Prop := ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), (M6.Coordinates.blockPolynomial N h).degree < (N : WithBot ℕ)
def check_3 : Prop := ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.blockPolynomial N (M6.Coordinates.coefficients N p) = p
def check_4 : Prop := ∀ (N : ℕ) [NeZero N], (AdjoinRoot.root (M6.Cyclic.modulus N))^N = 1
def check_5 : Prop := ∀ (N : ℕ) [NeZero N] (i j : ZMod N), M6.Coordinates.rootPow N (i+j) = M6.Coordinates.rootPow N i * M6.Coordinates.rootPow N j
def check_6 : Prop := ∀ (N : ℕ) [NeZero N], Function.Injective (M6.Coordinates.encode N)
def check_7 : Prop := ∀ (N : ℕ) [NeZero N], Function.Surjective (M6.Coordinates.encode N)
def check_8 : Prop := ∀ (N : ℕ) [NeZero N] (p : M6.Cyclic.BinaryPolynomial), p.degree < (N : WithBot ℕ) → M6.Coordinates.encode N (M6.Coordinates.coefficients N p) = M6.Cyclic.image N p
def check_9 : Prop := ∀ (N : ℕ) [NeZero N] (h : M6.Physical.Block N), M6.Coordinates.encode N h = ∑ i : ZMod N, AdjoinRoot.of (M6.Cyclic.modulus N) (h i) * M6.Coordinates.rootPow N i
def check_10 : Prop := ∀ (N : ℕ) [NeZero N] (a h : M6.Physical.Block N), M6.Coordinates.encode N (M6.Physical.conv N a h) = M6.Coordinates.encode N a * M6.Coordinates.encode N h

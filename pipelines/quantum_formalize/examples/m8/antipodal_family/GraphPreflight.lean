import M8AntipodalFamily
def target_0 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.AntipodalFamily.support N ∧ (1 : ZMod N) ∈ M8.AntipodalFamily.support N ∧ ((N/2 : ℕ) : ZMod N) ∈ M8.AntipodalFamily.support N
def target_1 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.Supports.polynomial (M8.AntipodalFamily.support N) = M8.AntipodalFamily.polynomial N
def target_2 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.CoverageFoundation.FullDirection (M8.AntipodalFamily.support N)
def target_3 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.PhysicalBridge.Valid 4 (M8.AntipodalFamily.recipe N)
def target_4 : Prop := ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1)
def target_5 : Prop := ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^v)
def target_6 : Prop := ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) ∣ M6.Cyclic.modulus (2^v)
def target_7 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.polynomial N).Monic ∧ M8.AntipodalFamily.polynomial N ≠ 1 ∧ M8.AntipodalFamily.polynomial N ≠ 0 ∧ (M8.AntipodalFamily.polynomial N).natDegree = N/2+1
def target_8 : Prop := ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M7.RecipeSignature.signature (M8.AntipodalFamily.recipe N) = M8.AntipodalFamily.polynomial N
def target_9 : Prop := ∀ (v : ℕ), 3 ≤ v → M8.Cutoff.limit (2^v) = v ∧ v < 2^(v-1)
def target_10 : Prop := ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → (M8.AntipodalFamily.polynomial N).degree < (N : WithBot ℕ)

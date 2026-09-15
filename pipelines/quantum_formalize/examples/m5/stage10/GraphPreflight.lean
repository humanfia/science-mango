import M5RepairSupport
import M5QuotientMonomialPeriod
#check (∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card)
#check (∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q)
#check (∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L)
#check (∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)))
#check (∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1)
#check (∀ (A : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport A))

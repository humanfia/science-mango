import M5PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T : ℕ) (A B : Finset ℕ) (e : ℕ), e ∈ A → M5.Connectivity.supportGcd T A B = 1 → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd A B e)) e = 1

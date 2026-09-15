import M5IntegerMobius


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N d : ℕ) (A B : Finset ℕ), d ∣ M5.Connectivity.supportGcd N A B ↔ d ∣ N ∧ (∀ a ∈ A, d ∣ a) ∧ (∀ b ∈ B, d ∣ b)

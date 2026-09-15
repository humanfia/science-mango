import M5CRT


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p δ T e : ℕ, p.Prime → p ∣ δ → Nat.gcd (Nat.gcd T δ) e = 1 → ¬ p ∣ e + M5.CRT.repairResidue e p * T

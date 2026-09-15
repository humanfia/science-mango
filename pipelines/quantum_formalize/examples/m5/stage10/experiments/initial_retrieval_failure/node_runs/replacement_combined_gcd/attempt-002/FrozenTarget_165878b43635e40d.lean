import M5QuotientMonomialPeriod
import M5RepairSupport


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))

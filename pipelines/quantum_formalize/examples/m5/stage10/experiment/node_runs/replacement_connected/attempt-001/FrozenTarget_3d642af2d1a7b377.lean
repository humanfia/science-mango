import M5QuotientMonomialPeriod
import M5RepairSupport

theorem M5.RepairSupport.replacement_combined_gcd : ∀ (A B : Finset ℕ) (e q : ℕ), M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) := by
  intro A B e q
  unfold M5.RepairSupport.combinedGcd M5.RepairSupport.repaired
  rw [Finset.gcd_insert]
  change Nat.gcd (Nat.gcd q ((A.erase e).gcd id)) (B.gcd id) = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))
  exact Nat.gcd_assoc q ((A.erase e).gcd id) (B.gcd id)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (e q : ℕ), Nat.gcd (Nat.gcd ((A.erase e).gcd id) (B.gcd id)) q = 1 → M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired A e q) B = 1

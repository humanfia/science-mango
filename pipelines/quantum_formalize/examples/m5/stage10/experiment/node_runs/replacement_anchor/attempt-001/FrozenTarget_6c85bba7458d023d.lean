import M5QuotientMonomialPeriod
import M5RepairSupport


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q

import M5QuotientMonomialPeriod
import M5RepairSupport


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A : Finset ℕ) (e q L : ℕ), (∀ a ∈ A, a < L) → q < L → ∀ a ∈ M5.RepairSupport.repaired A e q, a < L

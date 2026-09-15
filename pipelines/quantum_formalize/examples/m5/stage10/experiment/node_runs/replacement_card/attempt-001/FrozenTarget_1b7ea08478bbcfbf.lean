import M5QuotientMonomialPeriod
import M5RepairSupport


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A : Finset ℕ) (e q : ℕ), e ∈ A → q ∉ A → (M5.RepairSupport.repaired A e q).card = A.card

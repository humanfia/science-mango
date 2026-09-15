import M5QuotientMonomialPeriod
import M5RepairSupport


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) = AdjoinRoot.mk (M5.cyclicModulus T) (M5.SupportPolynomial.ofSupport A)

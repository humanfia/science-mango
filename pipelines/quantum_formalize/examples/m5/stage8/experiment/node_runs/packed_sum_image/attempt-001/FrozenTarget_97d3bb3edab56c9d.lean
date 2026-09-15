import M5PackingInjective
import M5SupportPolynomial


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r : Fin w → Fin T), Function.Injective (M5.Packing.packedValue r) → M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r) = ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ M5.Packing.packedValue r i

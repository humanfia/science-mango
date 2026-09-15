import FrozenTarget_08e627dc71059c5a
theorem M5.Period.period_cardinality_bound : QuantumHarnessFrozenTarget := by
  change ∀ F : M5.BinaryPolynomial, F.Monic → F.coeff 0 = 1 → M5.signaturePeriod F ≤ 2 ^ F.natDegree
  intro F hF h0
  letI : Finite (AdjoinRoot F) := M5.Period.quotient_finite F hF
  unfold M5.signaturePeriod
  calc
    orderOf (AdjoinRoot.root F) ≤ Nat.card (AdjoinRoot F) := orderOf_le_card _
    _ = 2 ^ F.natDegree := M5.Period.quotient_cardinality F hF

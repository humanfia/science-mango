import M5ConditionalResidueCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P ZA ZB : M5.BinaryPolynomial) (T d k l : ℕ), P.Monic → 0 < T → d ∣ T → M5.ConditionalResidueCount.RSelected P ZA T d k * M5.ConditionalResidueCount.RSelected P ZB T d l = ∑ a : Fin k → Fin T, ∑ b : Fin l → Fin T, M5.ConditionalResidueCount.divisibilityIndicator P ZA ZB d a b

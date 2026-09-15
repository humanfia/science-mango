import M5AnchoredTupleCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ T d : ℕ, 0 < T → d ∣ T → ∃ e : Fin (T / d) ≃ {r : Fin T // d ∣ r.val}, ∀ j : Fin (T / d), (e j).val.val = d * j.val

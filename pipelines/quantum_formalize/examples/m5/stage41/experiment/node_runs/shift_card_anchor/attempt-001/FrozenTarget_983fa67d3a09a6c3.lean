import M5Translation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), c ∈ S → (M5.Translation.shift S (-c)).card = S.card ∧ 0 ∈ M5.Translation.shift S (-c)

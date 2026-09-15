import M5Translation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (c : ZMod N), M5.Translation.differences (M5.Translation.shift S c) = M5.Translation.differences S

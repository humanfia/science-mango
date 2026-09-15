import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Pinned.Vector m) (i : Fin m) (b : ZMod 2), P i = none → (M6.Pinned.agrees (M6.Pinned.pin P i b) v ↔ M6.Pinned.agrees P v ∧ v i = b)

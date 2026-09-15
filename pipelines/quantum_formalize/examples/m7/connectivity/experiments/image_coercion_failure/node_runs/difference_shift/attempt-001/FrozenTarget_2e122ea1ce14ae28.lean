import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A

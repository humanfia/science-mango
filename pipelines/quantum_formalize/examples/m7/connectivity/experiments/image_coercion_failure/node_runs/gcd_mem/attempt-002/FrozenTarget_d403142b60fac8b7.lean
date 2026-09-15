import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H

import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤

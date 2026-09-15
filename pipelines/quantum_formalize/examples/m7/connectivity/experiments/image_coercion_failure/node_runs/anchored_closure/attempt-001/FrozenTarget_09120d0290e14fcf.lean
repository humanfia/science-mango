import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → AddSubgroup.closure (M7.Connectivity.differences A ∪ M7.Connectivity.differences B) = AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))

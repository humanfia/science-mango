import M7Connectivity


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (fun a : ℕ => (a : ZMod N)) '' ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B : Finset ℕ) : Set ℕ) = (A : Set (ZMod N)) ∪ (B : Set (ZMod N))

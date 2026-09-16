import M8CoverageFoundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ q : ℕ, 2 ≤ q → q ∣ N → AddSubgroup.zmultiples (q : ZMod N) ≠ ⊤

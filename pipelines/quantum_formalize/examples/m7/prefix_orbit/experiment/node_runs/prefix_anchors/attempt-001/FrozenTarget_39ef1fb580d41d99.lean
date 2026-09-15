import M7PrefixOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (A B WA WB : Finset ℕ) (y : M7.Action.Recipe N), M7.PrefixCompleted.Base N A B WA WB → M7.PrefixOrbit.Within A WA y.1 → M7.PrefixOrbit.Within B WB y.2 → (0 : ZMod N) ∈ y.1 ∧ (0 : ZMod N) ∈ y.2

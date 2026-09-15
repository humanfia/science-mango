import M7ClosedSolve


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M6.Final.PointwiseCorrect N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)

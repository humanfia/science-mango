import M7LabelReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (d : ℕ) (P : M6.Pinned.Pins (2*N)) (xs : List (Fin (2*N))), (M7.LabelReplay.endpoint P (M7.LabelReplay.trace c d P xs), M7.LabelReplay.queryCount (M7.LabelReplay.trace c d P xs)) = M6.Pinned.recover (fun P => (M7.LabelReplay.Q c P).coeff d) P xs

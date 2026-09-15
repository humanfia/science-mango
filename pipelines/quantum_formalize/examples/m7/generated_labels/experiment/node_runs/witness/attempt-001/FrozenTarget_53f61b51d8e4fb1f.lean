import M7GeneratedLabels


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ (i : Fin (M7.GeneratedFamily.size N w E)) (g : M7.Action.Record N) (d k : ℕ) (v : M6.Pinned.Vector (2*N)), M6.ActualTransfer.solve N (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1) (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2) = some (d,v,k) → M7.Transport.distance (M7.Action.act g (M7.GeneratedFamily.family N w E i)) = some d ∧ M7.Transport.Xmap g v ∈ M7.Transport.LX (M7.Action.act g (M7.GeneratedFamily.family N w E i)) ∧ M6.Pinned.weight (M7.Transport.Xmap g v) = d ∧ M6.Flatten.J N (M7.Transport.Xmap g v) ∈ M7.Transport.LZ (M7.Action.act g (M7.GeneratedFamily.family N w E i)) ∧ M6.Pinned.weight (M6.Flatten.J N (M7.Transport.Xmap g v)) = d ∧ k ≤ 2*N

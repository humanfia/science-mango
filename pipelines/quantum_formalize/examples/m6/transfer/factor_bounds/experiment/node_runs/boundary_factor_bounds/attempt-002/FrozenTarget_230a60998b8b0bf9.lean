import M6TransferFactorBounds


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) ≤ 1 ∧ (M6.Character.boundaryFactor P i s).natDegree ≤ 1

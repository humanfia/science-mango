import M7OrbitResidual


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ C bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.Separated bases → (∑ c ∈ bases, M7.ActualOrbit.distinctCount c (fun y => y ∈ C)) = (C ∩ M7.OrbitResidual.covered bases).card

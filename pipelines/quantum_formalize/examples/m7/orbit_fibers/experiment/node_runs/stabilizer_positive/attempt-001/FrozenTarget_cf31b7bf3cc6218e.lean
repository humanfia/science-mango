import M7OrbitFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), 0 < M7.OrbitFibers.stabilizerCount G c

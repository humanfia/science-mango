import M7OrbitFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ g₀ : G, Nonempty ({h : G // h • c = c} ≃ {g : G // g • c = g₀ • c})

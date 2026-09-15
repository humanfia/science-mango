import M7OrbitFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ (P : X → Prop) (test : X → Bool), M7.OrbitFibers.orbitCount G c P = M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = false) + M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = true)

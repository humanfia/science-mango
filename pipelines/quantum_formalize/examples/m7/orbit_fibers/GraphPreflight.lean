import M7OrbitFibers
open scoped BigOperators
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ g₀ : G, Nonempty ({h : G // h • c = c} ≃ {g : G // g • c = g₀ • c}))
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), 0 < M7.OrbitFibers.stabilizerCount G c)
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ y ∈ M7.OrbitFibers.orbit G c, M7.OrbitFibers.fiberCount G c y = M7.OrbitFibers.stabilizerCount G c)
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P = M7.OrbitFibers.orbitCount G c P * M7.OrbitFibers.stabilizerCount G c)
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P / M7.OrbitFibers.stabilizerCount G c = M7.OrbitFibers.orbitCount G c P ∧ M7.OrbitFibers.stabilizerCount G c ∣ M7.OrbitFibers.actionCount G c P)
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ (P : X → Prop) (test : X → Bool), M7.OrbitFibers.orbitCount G c P = M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = false) + M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = true))
#check (∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ (P : X → Prop) (test : X → Bool), M7.OrbitFibers.actionCount G c P = M7.OrbitFibers.actionCount G c (fun y => P y ∧ test y = false) + M7.OrbitFibers.actionCount G c (fun y => P y ∧ test y = true))

import M6BoundaryFibers
def check_0 : Prop := ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
def check_1 : Prop := ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0
def check_2 : Prop := ∀ (a b M : M6.BoundaryFibers.BP) (h k : AdjoinRoot M), M6.BoundaryFibers.boundary a b M (h+k) = M6.BoundaryFibers.boundary a b M h + M6.BoundaryFibers.boundary a b M k
def check_3 : Prop := ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0,0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0
def check_4 : Prop := ∀ (F M : M6.BoundaryFibers.BP), F.Monic → F ∣ M → M ≠ 0 → Nat.card {h : AdjoinRoot M // AdjoinRoot.mk M F * h = 0} = 2^F.natDegree
def check_5 : Prop := ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0,0)} = 2^(M6.Cyclic.signature a b M).natDegree
def check_6 : Prop := ∀ (a b M : M6.BoundaryFibers.BP), M ≠ 0 → ∀ h₀ : AdjoinRoot M, Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} = 2^(M6.Cyclic.signature a b M).natDegree

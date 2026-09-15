import M6KernelFibers
def check_0 : Prop := ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (h : M6.KernelFibers.BP), M6.KernelFibers.embed F K hF (AdjoinRoot.mk F h) = AdjoinRoot.mk (F*K) (K*h)
def check_1 : Prop := ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic), K ≠ 0 → Function.Injective (M6.KernelFibers.embed F K hF)
def check_2 : Prop := ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot F), AdjoinRoot.mk (F*K) F * M6.KernelFibers.embed F K hF z = 0
def check_3 : Prop := ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot (F*K)), AdjoinRoot.mk (F*K) F * z = 0 → ∃ t : AdjoinRoot F, M6.KernelFibers.embed F K hF t = z
def check_4 : Prop := ∀ (F : M6.KernelFibers.BP), F.Monic → Nat.card (AdjoinRoot F) = 2^F.natDegree
def check_5 : Prop := ∀ (F K : M6.KernelFibers.BP), F.Monic → K ≠ 0 → Nat.card (M6.KernelFibers.annihilator F K) = 2^F.natDegree

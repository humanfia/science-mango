import M6KernelFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (h : M6.KernelFibers.BP), M6.KernelFibers.embed F K hF (AdjoinRoot.mk F h) = AdjoinRoot.mk (F*K) (K*h)

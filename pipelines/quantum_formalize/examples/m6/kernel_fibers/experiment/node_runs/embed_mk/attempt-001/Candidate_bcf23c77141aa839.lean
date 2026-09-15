import FrozenTarget_bcf23c77141aa839
theorem M6.KernelFibers.embed_mk : QuantumHarnessFrozenTarget := by
  intro F K hF h
  change AdjoinRoot.mk (F * K)
      (K * AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h)) =
    AdjoinRoot.mk (F * K) (K * h)
  have hr := AdjoinRoot.mk_leftInverse hF (AdjoinRoot.mk F h)
  change AdjoinRoot.mk F
      (AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h)) =
    AdjoinRoot.mk F h at hr
  rw [AdjoinRoot.mk_eq_mk] at hr ⊢
  rcases hr with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    K * AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h) - K * h =
        K * (AdjoinRoot.modByMonicHom hF (AdjoinRoot.mk F h) - h) := by ring
    _ = K * (F * q) := by rw [hq]
    _ = (F * K) * q := by ring

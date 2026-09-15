import FrozenTarget_bb29e88677d59638
theorem M6.KernelFibers.embed_annihilated : QuantumHarnessFrozenTarget := by
  intro F K hF z
  change AdjoinRoot.mk (F * K) F *
      AdjoinRoot.mk (F * K) (K * AdjoinRoot.modByMonicHom hF z) = 0
  rw [← map_mul, AdjoinRoot.mk_eq_zero]
  refine ⟨AdjoinRoot.modByMonicHom hF z, ?_⟩
  ring

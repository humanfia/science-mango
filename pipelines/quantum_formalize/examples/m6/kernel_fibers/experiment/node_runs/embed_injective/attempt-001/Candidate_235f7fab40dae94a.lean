import FrozenTarget_235f7fab40dae94a
theorem M6.KernelFibers.embed_injective : QuantumHarnessFrozenTarget := by
  change ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic), K ≠ 0 → Function.Injective (M6.KernelFibers.embed F K hF)
  intro F K hF hK x y
  refine AdjoinRoot.induction_on x ?_
  intro p
  refine AdjoinRoot.induction_on y ?_
  intro q hpq
  rw [M6.KernelFibers.embed_mk, M6.KernelFibers.embed_mk] at hpq
  rw [AdjoinRoot.mk_eq_mk] at hpq ⊢
  rcases hpq with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ hK
  calc
    K * (p - q) = K * p - K * q := by ring
    _ = (F * K) * r := hr
    _ = K * (F * r) := by ring

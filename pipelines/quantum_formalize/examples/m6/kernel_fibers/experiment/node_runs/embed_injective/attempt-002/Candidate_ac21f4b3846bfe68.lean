import FrozenTarget_ac21f4b3846bfe68
theorem M6.KernelFibers.embed_injective : QuantumHarnessFrozenTarget := by
  change ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic), K ≠ 0 → Function.Injective (M6.KernelFibers.embed F K hF)
  intro F K hF hK x y
  refine AdjoinRoot.induction_on F x ?_
  intro a
  refine AdjoinRoot.induction_on F y ?_
  intro b hab
  rw [M6.KernelFibers.embed_mk, M6.KernelFibers.embed_mk, AdjoinRoot.mk_eq_mk] at hab
  rw [AdjoinRoot.mk_eq_mk]
  rcases hab with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply mul_left_cancel₀ hK
  calc
    K * (a - b) = K * a - K * b := by ring
    _ = (F * K) * q := hq
    _ = K * (F * q) := by ring

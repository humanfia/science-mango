import FrozenTarget_4a843eb8dbaaeffb
theorem M6.KernelFibers.embed_surjective_kernel : QuantumHarnessFrozenTarget := by
  change ∀ (F K : M6.KernelFibers.BP) (hF : F.Monic) (z : AdjoinRoot (F * K)), AdjoinRoot.mk (F * K) F * z = 0 → ∃ t : AdjoinRoot F, M6.KernelFibers.embed F K hF t = z
  intro F K hF z hz
  obtain ⟨h, rfl⟩ : ∃ h : M6.KernelFibers.BP, AdjoinRoot.mk (F * K) h = z := by
    first
    | exact AdjoinRoot.mk_surjective _ _
    | exact AdjoinRoot.mk_surjective _
  rw [← map_mul, AdjoinRoot.mk_eq_zero] at hz
  rcases hz with ⟨q, hq⟩
  have hh : h = K * q := by
    apply mul_left_cancel₀ hF.ne_zero
    simpa only [mul_assoc] using hq
  refine ⟨AdjoinRoot.mk F q, ?_⟩
  rw [M6.KernelFibers.embed_mk, hh]

import FrozenTarget_0bf95d34449e70fc
theorem M7.OrbitFibers.fiber_equiv : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c g₀
  refine ⟨{
    toFun := fun h => ⟨g₀ * h.val, ?_⟩
    invFun := fun g => ⟨g₀⁻¹ * g.val, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }⟩
  · rw [mul_smul, h.property]
  · rw [mul_smul, g.property]
    simp
  · intro h
    apply Subtype.ext
    change g₀⁻¹ * (g₀ * h.val) = h.val
    simp
  · intro g
    apply Subtype.ext
    change g₀ * (g₀⁻¹ * g.val) = g.val
    simp

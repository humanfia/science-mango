import FrozenTarget_70c7a6e114185194
theorem M6.BoundaryFibers.fiber_card : QuantumHarnessFrozenTarget := by
  change ∀ (a b M : M6.BoundaryFibers.BP), M ≠ 0 → ∀ h₀ : AdjoinRoot M, Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} = 2 ^ (M6.Cyclic.signature a b M).natDegree
  intro a b M hM h₀
  have hsub (h k : AdjoinRoot M) :
      M6.BoundaryFibers.boundary a b M (h - k) =
        M6.BoundaryFibers.boundary a b M h - M6.BoundaryFibers.boundary a b M k := by
    unfold M6.BoundaryFibers.boundary
    apply Prod.ext <;> exact mul_sub _ _ _
  let e : {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0, 0)} ≃
      {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} :=
    { toFun := fun h => ⟨h.val + h₀, by
        rw [M6.BoundaryFibers.boundary_add, h.property]
        exact zero_add _⟩
      invFun := fun h => ⟨h.val - h₀, by
        rw [hsub, h.property]
        exact sub_self _⟩
      left_inv := by
        intro h
        apply Subtype.ext
        exact add_sub_cancel_right h.val h₀
      right_inv := by
        intro h
        apply Subtype.ext
        exact sub_add_cancel h.val h₀ }
  exact (Nat.card_congr e.symm).trans (M6.BoundaryFibers.kernel_card a b M hM)

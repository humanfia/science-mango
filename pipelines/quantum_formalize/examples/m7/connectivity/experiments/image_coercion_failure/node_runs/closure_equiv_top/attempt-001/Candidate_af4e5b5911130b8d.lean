import FrozenTarget_af4e5b5911130b8d
theorem M7.Connectivity.closure_equiv_top : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤
  intro N _ e S
  have transport (f : ZMod N ≃+ ZMod N) (T : Set (ZMod N))
      (h : AddSubgroup.closure T = ⊤) : AddSubgroup.closure (f '' T) = ⊤ := by
    have hle : AddSubgroup.closure T ≤
        (AddSubgroup.closure (f '' T)).comap f.toAddMonoidHom := by
      apply AddSubgroup.closure_le.mpr
      intro x hx
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
    apply top_unique
    intro y _
    have hx : f.symm y ∈ AddSubgroup.closure T := by
      rw [h]
      trivial
    have hy := hle hx
    change f (f.symm y) ∈ AddSubgroup.closure (f '' T) at hy
    simpa using hy
  constructor
  · intro h
    simpa [Set.image_image] using transport e.symm (e '' S) h
  · exact transport e S

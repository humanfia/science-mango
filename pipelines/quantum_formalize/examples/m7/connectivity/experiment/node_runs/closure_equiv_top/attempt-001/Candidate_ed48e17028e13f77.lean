import FrozenTarget_ed48e17028e13f77
theorem M7.Connectivity.closure_equiv_top : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤
  intro N inst e S
  constructor
  · intro h
    have hle : AddSubgroup.closure (e '' S) ≤
        (AddSubgroup.closure S).comap e.symm.toAddMonoidHom := by
      apply (AddSubgroup.closure_le _).mpr
      rintro y ⟨x, hx, rfl⟩
      change e.symm (e x) ∈ AddSubgroup.closure S
      simpa using (AddSubgroup.subset_closure hx)
    apply top_unique
    intro x hx
    have hm : e x ∈ AddSubgroup.closure (e '' S) := by
      rw [h]
      trivial
    have hm' := hle hm
    change e.symm (e x) ∈ AddSubgroup.closure S at hm'
    simpa using hm'
  · intro h
    have hle : AddSubgroup.closure S ≤
        (AddSubgroup.closure (e '' S)).comap e.toAddMonoidHom := by
      apply (AddSubgroup.closure_le _).mpr
      intro x hx
      change e x ∈ AddSubgroup.closure (e '' S)
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
    apply top_unique
    intro x hx
    have hm : e.symm x ∈ AddSubgroup.closure S := by
      rw [h]
      trivial
    have hm' := hle hm
    change e (e.symm x) ∈ AddSubgroup.closure (e '' S) at hm'
    simpa using hm'

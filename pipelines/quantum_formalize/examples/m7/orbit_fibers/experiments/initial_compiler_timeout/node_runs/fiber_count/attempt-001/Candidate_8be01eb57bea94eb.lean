import FrozenTarget_8be01eb57bea94eb
theorem M7.OrbitFibers.fiber_count : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c y hy
  classical
  unfold M7.OrbitFibers.orbit at hy
  obtain ⟨g₀, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨e⟩ := M7.OrbitFibers.fiber_equiv G X c g₀
  unfold M7.OrbitFibers.fiberCount M7.OrbitFibers.stabilizerCount
  refine Finset.card_bij
    (fun g hg => (e.symm ⟨g, (Finset.mem_filter.mp hg).2⟩).val) ?_ ?_ ?_
  · intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.symm ⟨g, (Finset.mem_filter.mp hg).2⟩).property⟩
  · intro a ha b hb hab
    have h : e.symm ⟨a, (Finset.mem_filter.mp ha).2⟩ =
        e.symm ⟨b, (Finset.mem_filter.mp hb).2⟩ := Subtype.ext hab
    exact congrArg Subtype.val (e.symm.injective h)
  · intro h hh
    let h' : {h : G // h • c = c} := ⟨h, (Finset.mem_filter.mp hh).2⟩
    have hg : (e h').val ∈ Finset.univ.filter (fun g : G => g • c = g₀ • c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e h').property⟩
    refine ⟨(e h').val, hg, ?_⟩
    change (e.symm (e h')).val = h
    exact congrArg Subtype.val (e.symm_apply_apply h')

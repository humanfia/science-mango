import FrozenTarget_6ca6ea1751389617
theorem M8.Coverage.mixed_recognized : QuantumHarnessFrozenTarget := by
  intro N inst hN
  have hs : M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a := M8.MixedFamily.signature N hN
  have hd := M8.MixedFamily.support_data N hN
  have hl : (0 : ZMod N) ∈ (M8.MixedFamily.recipe N).1 := hd.2.2.1
  have hr : (0 : ZMod N) ∈ (M8.MixedFamily.recipe N).2 := hd.2.2.2.1
  have ht : M8.Anchor.trial (M8.MixedFamily.recipe N) false 1 0 0 = M8.MixedFamily.recipe N := by
    simp [M8.Anchor.trial, M8.Anchor.record, M7.Action.act, M7.Action.affine]
  have he : M8.Anchor.Eligible (M8.MixedFamily.recipe N) false 0 0 := by
    simpa [M8.Anchor.Eligible] using And.intro hl hr
  have ho : M8.OrbitSpan.value (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.anchor_minimum N (M8.MixedFamily.recipe N) ⟨0, hl⟩ ⟨0, hr⟩ (M8.Cutoff.limit N)).2
    refine ⟨false, 1, 0, 0, he, ?_⟩
    rw [ht]
    exact M8.MixedFamily.span_cutoff N hN
  refine ⟨?_, hs, ?_, M8.MixedNonproduct.orbit_nonproduct N hN⟩
  · apply (M8.Solver.recognized_exact N (M8.MixedFamily.recipe N) 2 (by decide) (M8.MixedFamily.valid N hN)).2
    refine ⟨?_, ho⟩
    rw [hs]
    exact M8.MixedFamily.nontrivial.1
  · intro g
    apply M8.CoverageFoundation.orbit_no_separated N (M8.MixedFamily.recipe N) g
    exact Or.inl (M8.MixedFamily.full_direction N hN)

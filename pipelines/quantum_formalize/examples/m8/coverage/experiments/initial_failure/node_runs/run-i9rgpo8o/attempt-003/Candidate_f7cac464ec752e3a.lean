import FrozenTarget_f7cac464ec752e3a
theorem M8.Coverage.mixed_recognized : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst hN
  have hv := M8.MixedFamily.valid N hN
  have hs : M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a := M8.MixedFamily.signature N hN
  rcases M8.MixedFamily.support_data N hN with ⟨_, _, hL, hR, _⟩
  have ht : M8.Anchor.trial (M8.MixedFamily.recipe N) false 1 0 0 = M8.MixedFamily.recipe N := by
    simp [M8.Anchor.trial, M8.Anchor.record, M7.Action.act, M7.Action.affine]
  have ho : M8.OrbitSpan.value (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.anchor_minimum N (M8.MixedFamily.recipe N) ⟨0, hL⟩ ⟨0, hR⟩ (M8.Cutoff.limit N)).2
    refine ⟨false, 1, 0, 0, ?_, ?_⟩
    · simpa [M8.Anchor.Eligible, M8.MixedFamily.recipe] using And.intro hL hR
    · rw [ht]
      exact M8.MixedFamily.span_cutoff N hN
  refine ⟨?_, hs, ?_, M8.MixedNonproduct.orbit_nonproduct N hN⟩
  · apply (M8.Solver.recognized_exact N (M8.MixedFamily.recipe N) 2 (by omega) hv).2
    refine ⟨?_, ho⟩
    rw [hs]
    exact M8.MixedFamily.nontrivial.1
  · intro g
    apply M8.CoverageFoundation.orbit_no_separated N (M8.MixedFamily.recipe N) g
    exact Or.inl (M8.MixedFamily.full_direction N hN)

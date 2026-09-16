import FrozenTarget_884e564d0d6485d5
theorem M8.Coverage.p4_recognized : QuantumHarnessFrozenTarget := by
  intro N inst hN hEven
  have hv := M8.P4Family.valid N (by omega)
  have hp := M8.Coverage.p4_physical N hN hEven
  have hd : M7.Transport.distance (M8.P4Family.recipe N) = some 2 := hp.1
  have hz : (0 : ZMod N) ∈ M8.P4Family.support N := (M8.P4Family.support_data N (by omega)).2.1
  have hne : (M8.P4Family.support N).Nonempty := ⟨0, hz⟩
  let g : M7.Action.Record N := M8.Anchor.record false 1 0 0
  have hg : M7.Action.act g (M8.P4Family.recipe N) = M8.P4Family.recipe N := by
    simp [g, M8.Anchor.record, M7.Action.act]
    have ha : M7.Action.affine (1 : (ZMod N)ˣ) 0 = id := by
      funext x
      simp [M7.Action.affine]
    simpa only [ha, Finset.image_id]
  have hs : M8.OrbitSpan.value (M8.P4Family.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.small_iff N (M8.P4Family.recipe N) hne hne (M8.Cutoff.limit N)).2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      change (0 : ZMod N) ∈ M8.P4Family.support N ∧ (0 : ZMod N) ∈ M8.P4Family.support N
      exact ⟨hz, hz⟩
    · rw [hg]
      exact M8.P4Family.span_cutoff N (by omega)
  have hF : M8.PhysicalBridge.signature (M8.P4Family.recipe N) ≠ 1 := by
    intro h
    have hn := (M8.RawParameters.raw_noLogical N 4 (M8.P4Family.recipe N) (by omega) hv).1.mpr h
    rw [hd] at hn
    contradiction
  obtain ⟨d, z, choice, k, hr⟩ := (M8.Solver.recognized_exact N (M8.P4Family.recipe N) 4 (by omega) hv).2 ⟨hF, hs⟩
  have hc := M8.Solver.recognized_correct N (M8.P4Family.recipe N) 4 (by omega) hv _ d z choice k hr
  have he : d = 2 := Option.some.inj (hc.2.2.1.symm.trans hd)
  subst d
  refine ⟨⟨z, choice, k, hr⟩, ?_, ?_⟩
  · exact M8.P4Gcd.signature_even N hN hEven
  · intro a
    apply M8.CoverageFoundation.orbit_no_separated N (M8.P4Family.recipe N) a
    exact Or.inl (M8.P4Family.full_direction N (by omega))

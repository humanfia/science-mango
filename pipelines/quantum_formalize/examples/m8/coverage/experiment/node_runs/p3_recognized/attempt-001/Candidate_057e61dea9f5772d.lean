import FrozenTarget_057e61dea9f5772d
theorem M8.Coverage.p3_recognized : QuantumHarnessFrozenTarget := by
  intro N inst hN hdiv
  have hv := M8.P3Family.valid N hN
  have hp := M8.Coverage.p3_physical N hN hdiv
  have hs : M8.PhysicalBridge.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial := M8.P3Family.signature N hN hdiv
  have hz := (M8.P3Family.support_data N hN).2.1
  have hn : (M8.P3Family.support N).Nonempty := ⟨0, hz⟩
  have hsig : M8.PhysicalBridge.signature (M8.P3Family.recipe N) ≠ 1 := by
    intro h
    have he := (M8.RawParameters.raw_noLogical N 3 (M8.P3Family.recipe N) (by omega) hv).1.mpr h
    rw [hp.1] at he
    cases he
  let g : M7.Action.Record N := by
    constructor <;> first | exact false | exact (1 : (ZMod N)ˣ) | exact (0 : ZMod N)
  have hg : M7.Action.act g (M8.P3Family.recipe N) = M8.P3Family.recipe N := by
    simp [g, M7.Action.act, M7.Action.affine]
  have hspan : M8.OrbitSpan.value (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.small_iff N (M8.P3Family.recipe N) hn hn (M8.Cutoff.limit N)).mpr
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      change (0 : ZMod N) ∈ M8.P3Family.support N ∧ (0 : ZMod N) ∈ M8.P3Family.support N
      exact ⟨hz, hz⟩
    · rw [hg]
      exact M8.P3Family.span_cutoff N hN
  obtain ⟨d, z, choice, k, hr⟩ := (M8.Solver.recognized_exact N (M8.P3Family.recipe N) 3 (by omega) hv).mpr ⟨hsig, hspan⟩
  have hd := (M8.Solver.recognized_correct N (M8.P3Family.recipe N) 3 (by omega) hv _ d z choice k hr).2.2.1
  have hd2 : d = 2 := Option.some.inj (hd.symm.trans hp.1)
  subst d
  refine ⟨hs, ⟨z, choice, k, hr⟩, ?_⟩
  intro a
  apply M8.CoverageFoundation.orbit_no_separated N (M8.P3Family.recipe N) a
  exact Or.inl (M8.P3Family.full_direction N hN)

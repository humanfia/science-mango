import FrozenTarget_d04a6b457ed0d11c
theorem M7.Transport.distance_invariant : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hd (r : M7.Transport.Recipe N) :
      M7.Transport.distance r = M6.Pinned.distance (M7.Transport.LX r) := by
    let a := M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)
    let b := M6.Coordinates.coefficients N (M7.Supports.polynomial r.2)
    change M6.CSS.quantumDistance
      (M6.Spaces.boundaryWords N a b) (M6.Spaces.cycleWords N a b)
      (M6.Character.subspaceWords (M6.Spaces.D N a b))
      (M6.Character.dualWords (M6.Spaces.B N a b)) = _
    rw [M6.ActualCSS.common_quantum_distance]
    simp only [a, b, M7.Domain.coefficients_indicator]
    rfl
  rw [hd, hd]
  have hw := M7.Transport.weight_sets N g c
  have hn : (M7.Transport.LX (M7.Action.act g c)).Nonempty ↔
      (M7.Transport.LX c).Nonempty := by
    have h : ((M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight).Nonempty ↔
        ((M7.Transport.LX c).image M6.Pinned.weight).Nonempty := by
      rw [hw]
    simpa only [Finset.image_nonempty] using h
  have hm (d : ℕ) :
      (∃ v ∈ M7.Transport.LX (M7.Action.act g c), M6.Pinned.weight v = d) ↔
      (∃ v ∈ M7.Transport.LX c, M6.Pinned.weight v = d) := by
    have h : d ∈ (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight ↔
        d ∈ (M7.Transport.LX c).image M6.Pinned.weight := by
      rw [hw]
    simpa only [Finset.mem_image] using h
  cases hdist : M6.Pinned.distance (M7.Transport.LX c) with
  | none =>
      apply (M6.Pinned.distance_spec (2*N) _).1.mpr
      have he := (M6.Pinned.distance_spec (2*N) _).1.mp hdist
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro v hv
      obtain ⟨w, hw⟩ := hn.mp ⟨v, hv⟩
      simpa [he] using hw
  | some d =>
      apply (M6.Pinned.distance_spec (2*N) _).2 d |>.mpr
      obtain ⟨hex, hmin⟩ := (M6.Pinned.distance_spec (2*N) _).2 d |>.mp hdist
      refine ⟨(hm d).mpr hex, ?_⟩
      intro v hv
      obtain ⟨w, hw, heq⟩ := (hm (M6.Pinned.weight v)).mp ⟨v, hv, rfl⟩
      rw [← heq]
      exact hmin w hw

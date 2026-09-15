import FrozenTarget_5caae27621323919
theorem M7.Transport.distance_invariant : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hd : ∀ r : M7.Transport.Recipe N,
      M7.Transport.distance r = M6.Pinned.distance (M7.Transport.LX r) := by
    intro r
    change M6.CSS.quantumDistance
      (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)) (M6.Coordinates.coefficients N (M7.Supports.polynomial r.2)))
      (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)) (M6.Coordinates.coefficients N (M7.Supports.polynomial r.2)))
      (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)) (M6.Coordinates.coefficients N (M7.Supports.polynomial r.2))))
      (M6.Character.dualWords (M6.Spaces.B N (M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)) (M6.Coordinates.coefficients N (M7.Supports.polynomial r.2)))) = _
    simp only [M7.Domain.coefficients_indicator, M6.ActualCSS.common_quantum_distance]
    rfl
  rw [hd, hd]
  let A := M7.Transport.LX (M7.Action.act g c)
  let B := M7.Transport.LX c
  have hw : A.image M6.Pinned.weight = B.image M6.Pinned.weight :=
    M7.Transport.weight_sets N g c
  change M6.Pinned.distance A = M6.Pinned.distance B
  have hm (d : ℕ) :
      (∃ v ∈ A, M6.Pinned.weight v = d) ↔
      (∃ v ∈ B, M6.Pinned.weight v = d) := by
    change d ∈ A.image M6.Pinned.weight ↔ d ∈ B.image M6.Pinned.weight
    rw [hw]
  cases hb : M6.Pinned.distance B with
  | none =>
      apply (M6.Pinned.distance_spec (2*N) A).1.mpr
      have he := (M6.Pinned.distance_spec (2*N) B).1.mp hb
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨w, hwB, _⟩ := (hm (M6.Pinned.weight v)).mp ⟨v, hv, rfl⟩
      simpa [he] using hwB
  | some d =>
      obtain ⟨hex, hmin⟩ := (M6.Pinned.distance_spec (2*N) B).2 d |>.mp hb
      apply (M6.Pinned.distance_spec (2*N) A).2 d |>.mpr
      refine ⟨(hm d).mpr hex, ?_⟩
      intro v hv
      obtain ⟨w, hwB, heq⟩ := (hm (M6.Pinned.weight v)).mp ⟨v, hv, rfl⟩
      exact heq ▸ hmin w hwB

import FrozenTarget_7984ffeefe370432
theorem M6.CSS.css_distance_min : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ hBX hBZ hXC hZC
  classical
  have hX0 : (0 : M6.CSS.Vector m) ∈ CX := hXC hBX
  have hZ0 : (0 : M6.CSS.Vector m) ∈ CZ := hZC hBZ
  have hpX : ∀ v ∈ M6.CSS.logical BX CX,
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).mpr
    exact ⟨(Finset.mem_sdiff.mp hv).1, hZ0, Or.inl hv⟩
  have hpZ : ∀ v ∈ M6.CSS.logical BZ CZ,
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).mpr
    exact ⟨hX0, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have sX := M6.Pinned.distance_spec m (M6.CSS.logical BX CX)
  have sZ := M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)
  have sQ := M6.CSS.quantum_distance_spec m BX CX BZ CZ
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have eX := sX.1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have eZ := sZ.1.mp hz
      simp only [hx, hz, M6.CSS.minDistance]
      apply sQ.1.mpr
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hp | hp
      · simp [eX] at hp
      · simp [eZ] at hp
    | some dz =>
      obtain ⟨⟨v, hv, hw⟩, hb⟩ := (sZ.2 dz).mp hz
      simp only [hx, hz, M6.CSS.minDistance]
      apply (sQ.2 dz).mpr
      constructor
      · exact ⟨(0, v), hpZ v hv, (M6.CSS.pure_weights m v).2.trans hw⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hp | hp
        · simp [eX] at hp
        · exact (hb p.2 hp).trans (M6.CSS.support_bounds m p).2
  | some dx =>
    obtain ⟨⟨v, hv, hw⟩, hbX⟩ := (sX.2 dx).mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have eZ := sZ.1.mp hz
      simp only [hx, hz, M6.CSS.minDistance]
      apply (sQ.2 dx).mpr
      constructor
      · exact ⟨(v, 0), hpX v hv, (M6.CSS.pure_weights m v).1.trans hw⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hp | hp
        · exact (hbX p.1 hp).trans (M6.CSS.support_bounds m p).1
        · simp [eZ] at hp
    | some dz =>
      obtain ⟨⟨w, hwZ, hwgt⟩, hbZ⟩ := (sZ.2 dz).mp hz
      simp only [hx, hz, M6.CSS.minDistance]
      apply (sQ.2 (min dx dz)).mpr
      constructor
      · by_cases h : dx ≤ dz
        · refine ⟨(v, 0), hpX v hv, ?_⟩
          rw [(M6.CSS.pure_weights m v).1, hw, min_eq_left h]
        · refine ⟨(0, w), hpZ w hwZ, ?_⟩
          rw [(M6.CSS.pure_weights m w).2, hwgt, min_eq_right (le_of_not_ge h)]
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hp | hp
        · exact (min_le_left dx dz).trans ((hbX p.1 hp).trans (M6.CSS.support_bounds m p).1)
        · exact (min_le_right dx dz).trans ((hbZ p.2 hp).trans (M6.CSS.support_bounds m p).2)

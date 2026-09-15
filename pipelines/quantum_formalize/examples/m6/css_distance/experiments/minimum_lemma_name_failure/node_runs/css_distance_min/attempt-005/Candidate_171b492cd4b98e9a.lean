import FrozenTarget_171b492cd4b98e9a
theorem M6.CSS.css_distance_min : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ hBX hBZ hXC hZC
  classical
  have hpX : ∀ v ∈ M6.CSS.logical BX CX,
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).2
    exact ⟨(Finset.mem_sdiff.mp hv).1, hZC hBZ, Or.inl hv⟩
  have hpZ : ∀ v ∈ M6.CSS.logical BZ CZ,
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).2
    exact ⟨hXC hBX, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have qs := M6.CSS.quantum_distance_spec m BX CX BZ CZ
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have ex := (M6.Pinned.distance_spec m (M6.CSS.logical BX CX)).1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = none
      apply qs.1.mpr
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hp | hp
      · simpa [ex] using hp
      · simpa [ez] using hp
    | some dz =>
      change M6.CSS.quantumDistance BX CX BZ CZ = some dz
      obtain ⟨⟨v, hv, hw⟩, hb⟩ :=
        (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).2 dz |>.mp hz
      apply (qs.2 dz).mpr
      constructor
      · exact ⟨(0, v), hpZ v hv, (M6.CSS.pure_weights m v).2.trans hw⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hp | hp
        · have hf : False := by simpa [ex] using hp
          exact hf.elim
        · exact (hb p.2 hp).trans (M6.CSS.support_bounds m p).2
  | some dx =>
    obtain ⟨⟨vx, hvx, hwx⟩, hbx⟩ :=
      (M6.Pinned.distance_spec m (M6.CSS.logical BX CX)).2 dx |>.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some dx
      apply (qs.2 dx).mpr
      constructor
      · exact ⟨(vx, 0), hpX vx hvx, (M6.CSS.pure_weights m vx).1.trans hwx⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hp | hp
        · exact (hbx p.1 hp).trans (M6.CSS.support_bounds m p).1
        · have hf : False := by simpa [ez] using hp
          exact hf.elim
    | some dz =>
      obtain ⟨⟨vz, hvz, hwz⟩, hbz⟩ :=
        (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).2 dz |>.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some (min dx dz)
      apply (qs.2 (min dx dz)).mpr
      constructor
      · by_cases h : dx ≤ dz
        · refine ⟨(vx, 0), hpX vx hvx, ?_⟩
          simpa [min_eq_left h] using (M6.CSS.pure_weights m vx).1.trans hwx
        · refine ⟨(0, vz), hpZ vz hvz, ?_⟩
          simpa [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using
            (M6.CSS.pure_weights m vz).2.trans hwz
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hp | hp
        · exact (min_le_left dx dz).trans ((hbx p.1 hp).trans (M6.CSS.support_bounds m p).1)
        · exact (min_le_right dx dz).trans ((hbz p.2 hp).trans (M6.CSS.support_bounds m p).2)

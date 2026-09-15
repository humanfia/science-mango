import FrozenTarget_181be3f5aa0b3682
theorem M6.CSS.css_distance_min : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ hBX hBZ hXC hZC
  classical
  have pureX : ∀ v ∈ M6.CSS.logical BX CX,
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).2
    exact ⟨(Finset.mem_sdiff.mp hv).1, hZC hBZ, Or.inl hv⟩
  have pureZ : ∀ v ∈ M6.CSS.logical BZ CZ,
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    intro v hv
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).2
    exact ⟨hXC hBX, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have sx := M6.Pinned.distance_spec m (M6.CSS.logical BX CX)
  have sz := M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)
  have sq := M6.CSS.quantum_distance_spec m BX CX BZ CZ
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have ex := sx.1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      simp only [M6.CSS.minDistance]
      apply sq.1.mpr
      apply Finset.ext
      intro p
      constructor
      · intro hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hpX | hpZ
        · rw [ex] at hpX
          exact False.elim (Finset.not_mem_empty _ hpX)
        · rw [ez] at hpZ
          exact False.elim (Finset.not_mem_empty _ hpZ)
      · intro hp
        exact False.elim (Finset.not_mem_empty _ hp)
    | some dz =>
      simp only [M6.CSS.minDistance]
      obtain ⟨⟨v, hv, hw⟩, hb⟩ := (sz.2 dz).mp hz
      apply (sq.2 dz).mpr
      constructor
      · exact ⟨(0, v), pureZ v hv, (M6.CSS.pure_weights m v).2.trans hw⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hpX | hpZ
        · rw [ex] at hpX
          exact False.elim (Finset.not_mem_empty _ hpX)
        · exact (hb p.2 hpZ).trans (M6.CSS.support_bounds m p).2
  | some dx =>
    obtain ⟨⟨vx, hvx, hwx⟩, hbx⟩ := (sx.2 dx).mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      simp only [M6.CSS.minDistance]
      apply (sq.2 dx).mpr
      constructor
      · exact ⟨(vx, 0), pureX vx hvx, (M6.CSS.pure_weights m vx).1.trans hwx⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hpX | hpZ
        · exact (hbx p.1 hpX).trans (M6.CSS.support_bounds m p).1
        · rw [ez] at hpZ
          exact False.elim (Finset.not_mem_empty _ hpZ)
    | some dz =>
      obtain ⟨⟨vz, hvz, hwz⟩, hbz⟩ := (sz.2 dz).mp hz
      simp only [M6.CSS.minDistance]
      apply (sq.2 (min dx dz)).mpr
      constructor
      · by_cases h : dx ≤ dz
        · rw [min_eq_left h]
          exact ⟨(vx, 0), pureX vx hvx, (M6.CSS.pure_weights m vx).1.trans hwx⟩
        · rw [min_eq_right (le_of_not_ge h)]
          exact ⟨(0, vz), pureZ vz hvz, (M6.CSS.pure_weights m vz).2.trans hwz⟩
      · intro p hp
        rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hpX | hpZ
        · exact (min_le_left dx dz).trans ((hbx p.1 hpX).trans (M6.CSS.support_bounds m p).1)
        · exact (min_le_right dx dz).trans ((hbz p.2 hpZ).trans (M6.CSS.support_bounds m p).2)

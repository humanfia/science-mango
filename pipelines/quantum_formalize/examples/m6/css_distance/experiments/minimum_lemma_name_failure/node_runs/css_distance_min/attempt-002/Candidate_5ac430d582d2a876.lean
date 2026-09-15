import FrozenTarget_5ac430d582d2a876
theorem M6.CSS.css_distance_min : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ))
  intro m BX CX BZ CZ hBX hBZ hXC hZC
  classical
  have hpX (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BX CX) :
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).2
    exact ⟨(Finset.mem_sdiff.mp hv).1, hZC hBZ, Or.inl hv⟩
  have hpZ (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BZ CZ) :
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).2
    exact ⟨hXC hBX, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have hs (d : ℕ)
      (hw : (∃ v ∈ M6.CSS.logical BX CX, M6.Pinned.weight v = d) ∨
        (∃ v ∈ M6.CSS.logical BZ CZ, M6.Pinned.weight v = d))
      (hlX : ∀ v ∈ M6.CSS.logical BX CX, d ≤ M6.Pinned.weight v)
      (hlZ : ∀ v ∈ M6.CSS.logical BZ CZ, d ≤ M6.Pinned.weight v) :
      M6.CSS.quantumDistance BX CX BZ CZ = some d := by
    apply (M6.CSS.quantum_distance_spec m BX CX BZ CZ).2 d |>.mpr
    constructor
    · rcases hw with ⟨v, hv, hd⟩ | ⟨v, hv, hd⟩
      · exact ⟨(v, 0), hpX v hv, (M6.CSS.pure_weights m v).1.trans hd⟩
      · exact ⟨(0, v), hpZ v hv, (M6.CSS.pure_weights m v).2.trans hd⟩
    · intro p hp
      rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hx | hz
      · exact (hlX p.1 hx).trans (M6.CSS.support_bounds m p).1
      · exact (hlZ p.2 hz).trans (M6.CSS.support_bounds m p).2
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have heX := (M6.Pinned.distance_spec m (M6.CSS.logical BX CX)).1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have heZ := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).1.mp hz
      have he : M6.CSS.logicalPaulis BX CX BZ CZ = ∅ := by
        apply Finset.ext
        intro p
        constructor
        · intro hp
          rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).1 hp).2.2 with hp | hp
          · simpa [heX] using hp
          · simpa [heZ] using hp
        · intro hp
          exact False.elim (Finset.not_mem_empty p hp)
      simpa [M6.CSS.minDistance] using
        (M6.CSS.quantum_distance_spec m BX CX BZ CZ).1.mpr he
    | some dz =>
      obtain ⟨hwZ, hlZ⟩ := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).2 dz |>.mp hz
      have hq := hs dz (Or.inr hwZ) (by
        intro v hv
        simp [heX] at hv) hlZ
      simpa [M6.CSS.minDistance] using hq
  | some dx =>
    obtain ⟨hwX, hlX⟩ := (M6.Pinned.distance_spec m (M6.CSS.logical BX CX)).2 dx |>.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have heZ := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).1.mp hz
      have hq := hs dx (Or.inl hwX) hlX (by
        intro v hv
        simp [heZ] at hv)
      simpa [M6.CSS.minDistance] using hq
    | some dz =>
      obtain ⟨hwZ, hlZ⟩ := (M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)).2 dz |>.mp hz
      have hw : (∃ v ∈ M6.CSS.logical BX CX, M6.Pinned.weight v = min dx dz) ∨
          (∃ v ∈ M6.CSS.logical BZ CZ, M6.Pinned.weight v = min dx dz) := by
        by_cases h : dx ≤ dz
        · exact Or.inl (by simpa [min_eq_left h] using hwX)
        · exact Or.inr (by simpa [min_eq_right (Nat.le_of_not_ge h)] using hwZ)
      have hq := hs (min dx dz) hw
        (fun v hv => (min_le_left dx dz).trans (hlX v hv))
        (fun v hv => (min_le_right dx dz).trans (hlZ v hv))
      simpa [M6.CSS.minDistance] using hq

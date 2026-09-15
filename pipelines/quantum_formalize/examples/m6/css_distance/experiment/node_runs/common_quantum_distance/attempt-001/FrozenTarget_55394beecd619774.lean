import M6CSSDistance
import M6PinnedAccepted

theorem M6.CSS.involution_distance : ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ := by
  classical
  change ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ
  intro m LX LZ J hJ hw hmem
  have hback (v : M6.CSS.Vector m) (hv : v ∈ LZ) : J v ∈ LX := by
    apply (hmem (J v)).mpr
    simpa only [hJ v] using hv
  cases hd : M6.Pinned.distance LX with
  | none =>
      have hX : LX = ∅ := (M6.Pinned.distance_spec m LX).1.mp hd
      have hZ : LZ = ∅ := by
        apply Finset.ext
        intro v
        constructor
        · intro hv
          have hx := hback v hv
          rw [hX] at hx
          simp at hx
        · intro hv
          simp at hv
      exact ((M6.Pinned.distance_spec m LZ).1.mpr hZ).symm
  | some d =>
      obtain ⟨⟨v, hv, hvw⟩, hmin⟩ := (M6.Pinned.distance_spec m LX).2 d |>.mp hd
      symm
      apply (M6.Pinned.distance_spec m LZ).2 d |>.mpr
      constructor
      · exact ⟨J v, (hmem v).mp hv, (hw v).trans hvw⟩
      · intro u hu
        have h := hmin (J u) (hback u hu)
        simpa only [hw u] using h

theorem M6.CSS.logical_pauli_components : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ p
  classical
  simp only [M6.CSS.logicalPaulis, M6.CSS.logical, Finset.mem_filter,
    Finset.mem_product, Finset.mem_sdiff] <;> tauto

theorem M6.CSS.pure_weights : ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v := by
  change ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v
  intro m v
  classical
  simp [M6.CSS.weight, M6.CSS.support, M6.Pinned.weight]

theorem M6.CSS.quantum_distance_spec : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (M6.CSS.quantumDistance BX CX BZ CZ = none ↔ M6.CSS.logicalPaulis BX CX BZ CZ = ∅) ∧ ∀ d : ℕ, (M6.CSS.quantumDistance BX CX BZ CZ = some d ↔ (∃ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, M6.CSS.weight p = d) ∧ ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p) := by
  classical
  intro m BX CX BZ CZ
  let L := M6.CSS.logicalPaulis BX CX BZ CZ
  have hdef : M6.CSS.logicalPaulis BX CX BZ CZ = L := rfl
  by_cases hL : L.Nonempty
  · have hs : (L.image M6.CSS.weight).Nonempty := hL.image M6.CSS.weight
    have hne : L ≠ ∅ := hL.ne_empty
    have hsne : L.image M6.CSS.weight ≠ ∅ := hs.ne_empty
    have hmin : ∀ d : ℕ,
        (L.image M6.CSS.weight).min' hs = d ↔
          (∃ p ∈ L, M6.CSS.weight p = d) ∧
            ∀ p ∈ L, d ≤ M6.CSS.weight p := by
      intro d
      constructor
      · intro hd
        subst d
        obtain ⟨p, hp, hw⟩ := Finset.mem_image.mp
          (Finset.min'_mem (L.image M6.CSS.weight) hs)
        refine ⟨⟨p, hp, hw⟩, ?_⟩
        intro q hq
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      · rintro ⟨⟨p, hp, hw⟩, hb⟩
        apply le_antisymm
        · rw [← hw]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        · obtain ⟨q, hq, hqw⟩ := Finset.mem_image.mp
            (Finset.min'_mem (L.image M6.CSS.weight) hs)
          rw [← hqw]
          exact hb q hq
    simp [M6.CSS.quantumDistance, hdef, hL, hs, hne, hsne, hmin]
  · have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [M6.CSS.quantumDistance, hdef, he]

theorem M6.CSS.support_bounds : ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p := by
  change ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p
  intro m p
  classical
  unfold M6.Pinned.weight M6.CSS.weight M6.CSS.support
  constructor
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inl hi
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Or.inr hi

theorem M6.CSS.css_distance_min : ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ))
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ hBX hBZ hBCX hBCZ
  classical
  have pureX (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BX CX) :
      (v, 0) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (v, 0)).mpr
    exact ⟨(Finset.mem_sdiff.mp hv).1, hBCZ hBZ, Or.inl hv⟩
  have pureZ (v : M6.CSS.Vector m) (hv : v ∈ M6.CSS.logical BZ CZ) :
      (0, v) ∈ M6.CSS.logicalPaulis BX CX BZ CZ := by
    apply (M6.CSS.logical_pauli_components m BX CX BZ CZ (0, v)).mpr
    exact ⟨hBCX hBX, (Finset.mem_sdiff.mp hv).1, Or.inr hv⟩
  have lower (d : ℕ)
      (hx : ∀ v ∈ M6.CSS.logical BX CX, d ≤ M6.Pinned.weight v)
      (hz : ∀ v ∈ M6.CSS.logical BZ CZ, d ≤ M6.Pinned.weight v) :
      ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p := by
    intro p hp
    rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hpX | hpZ
    · exact (hx p.1 hpX).trans (M6.CSS.support_bounds m p).1
    · exact (hz p.2 hpZ).trans (M6.CSS.support_bounds m p).2
  have sx := M6.Pinned.distance_spec m (M6.CSS.logical BX CX)
  have sz := M6.Pinned.distance_spec m (M6.CSS.logical BZ CZ)
  have sq := M6.CSS.quantum_distance_spec m BX CX BZ CZ
  cases hx : M6.Pinned.distance (M6.CSS.logical BX CX) with
  | none =>
    have ex := sx.1.mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = none
      apply sq.1.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      rcases ((M6.CSS.logical_pauli_components m BX CX BZ CZ p).mp hp).2.2 with hpX | hpZ
      · simpa [ex] using hpX
      · simpa [ez] using hpZ
    | some dz =>
      change M6.CSS.quantumDistance BX CX BZ CZ = some dz
      obtain ⟨⟨v, hv, hw⟩, hb⟩ := (sz.2 dz).mp hz
      apply (sq.2 dz).mpr
      refine ⟨⟨(0, v), pureZ v hv, (M6.CSS.pure_weights m v).2.trans hw⟩, ?_⟩
      apply lower dz
      · intro u hu
        simpa [ex] using hu
      · exact hb
  | some dx =>
    obtain ⟨⟨v, hv, hw⟩, hbX⟩ := (sx.2 dx).mp hx
    cases hz : M6.Pinned.distance (M6.CSS.logical BZ CZ) with
    | none =>
      have ez := sz.1.mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some dx
      apply (sq.2 dx).mpr
      refine ⟨⟨(v, 0), pureX v hv, (M6.CSS.pure_weights m v).1.trans hw⟩, ?_⟩
      apply lower dx hbX
      intro u hu
      simpa [ez] using hu
    | some dz =>
      obtain ⟨⟨w, hwz, hww⟩, hbZ⟩ := (sz.2 dz).mp hz
      change M6.CSS.quantumDistance BX CX BZ CZ = some (min dx dz)
      apply (sq.2 (min dx dz)).mpr
      constructor
      · by_cases h : dx ≤ dz
        · refine ⟨(v, 0), pureX v hv, ?_⟩
          simpa only [min_eq_left h] using (M6.CSS.pure_weights m v).1.trans hw
        · refine ⟨(0, w), pureZ w hwz, ?_⟩
          simpa only [min_eq_right (le_of_not_ge h)] using (M6.CSS.pure_weights m w).2.trans hww
      · apply lower (min dx dz)
        · intro u hu
          exact (min_le_left dx dz).trans (hbX u hu)
        · intro u hu
          exact (min_le_right dx dz).trans (hbZ u hu)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ M6.CSS.logical BX CX ↔ J v ∈ M6.CSS.logical BZ CZ) → M6.CSS.quantumDistance BX CX BZ CZ = M6.Pinned.distance (M6.CSS.logical BX CX)

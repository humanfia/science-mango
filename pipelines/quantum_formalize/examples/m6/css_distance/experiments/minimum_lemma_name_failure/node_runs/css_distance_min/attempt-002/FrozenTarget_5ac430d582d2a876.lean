import M6CSSDistance
import M6PinnedAccepted

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ))

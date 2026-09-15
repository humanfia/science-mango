import M6CSSDistance
import M6PinnedAccepted

noncomputable def M6.CSSTarget.support_bounds : Prop :=
  ∀ (m : ℕ) (p : M6.CSS.Pauli m), M6.Pinned.weight p.1 ≤ M6.CSS.weight p ∧ M6.Pinned.weight p.2 ≤ M6.CSS.weight p

#check M6.CSSTarget.support_bounds

noncomputable def M6.CSSTarget.pure_weights : Prop :=
  ∀ (m : ℕ) (v : M6.CSS.Vector m), M6.CSS.weight (v, 0) = M6.Pinned.weight v ∧ M6.CSS.weight (0, v) = M6.Pinned.weight v

#check M6.CSSTarget.pure_weights

noncomputable def M6.CSSTarget.logical_pauli_components : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (p : M6.CSS.Pauli m), p ∈ M6.CSS.logicalPaulis BX CX BZ CZ ↔ p.1 ∈ CX ∧ p.2 ∈ CZ ∧ (p.1 ∈ M6.CSS.logical BX CX ∨ p.2 ∈ M6.CSS.logical BZ CZ)

#check M6.CSSTarget.logical_pauli_components

noncomputable def M6.CSSTarget.quantum_distance_spec : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (M6.CSS.quantumDistance BX CX BZ CZ = none ↔ M6.CSS.logicalPaulis BX CX BZ CZ = ∅) ∧ ∀ d : ℕ, (M6.CSS.quantumDistance BX CX BZ CZ = some d ↔ (∃ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, M6.CSS.weight p = d) ∧ ∀ p ∈ M6.CSS.logicalPaulis BX CX BZ CZ, d ≤ M6.CSS.weight p)

#check M6.CSSTarget.quantum_distance_spec

noncomputable def M6.CSSTarget.css_distance_min : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → M6.CSS.quantumDistance BX CX BZ CZ = M6.CSS.minDistance (M6.Pinned.distance (M6.CSS.logical BX CX)) (M6.Pinned.distance (M6.CSS.logical BZ CZ))

#check M6.CSSTarget.css_distance_min

noncomputable def M6.CSSTarget.involution_distance : Prop :=
  ∀ (m : ℕ) (LX LZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ LX ↔ J v ∈ LZ) → M6.Pinned.distance LX = M6.Pinned.distance LZ

#check M6.CSSTarget.involution_distance

noncomputable def M6.CSSTarget.common_quantum_distance : Prop :=
  ∀ (m : ℕ) (BX CX BZ CZ : Finset (M6.CSS.Vector m)) (J : M6.CSS.Vector m → M6.CSS.Vector m), (0 : M6.CSS.Vector m) ∈ BX → (0 : M6.CSS.Vector m) ∈ BZ → BX ⊆ CX → BZ ⊆ CZ → Function.Involutive J → (∀ v, M6.Pinned.weight (J v) = M6.Pinned.weight v) → (∀ v, v ∈ M6.CSS.logical BX CX ↔ J v ∈ M6.CSS.logical BZ CZ) → M6.CSS.quantumDistance BX CX BZ CZ = M6.Pinned.distance (M6.CSS.logical BX CX)

#check M6.CSSTarget.common_quantum_distance


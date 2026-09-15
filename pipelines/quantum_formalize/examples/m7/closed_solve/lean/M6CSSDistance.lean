import M6Pinned

namespace M6.CSS

abbrev Vector (m : ℕ) := M6.Pinned.Vector m
abbrev Pauli (m : ℕ) := Vector m × Vector m

noncomputable def logical {m : ℕ} (B C : Finset (Vector m)) : Finset (Vector m) := C \ B

noncomputable def support {m : ℕ} (p : Pauli m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0)

noncomputable def weight {m : ℕ} (p : Pauli m) : ℕ := (support p).card

noncomputable def logicalPaulis {m : ℕ}
    (BX CX BZ CZ : Finset (Vector m)) : Finset (Pauli m) := by
  classical
  exact (CX ×ˢ CZ).filter (fun p => ¬ (p.1 ∈ BX ∧ p.2 ∈ BZ))

noncomputable def quantumDistance {m : ℕ}
    (BX CX BZ CZ : Finset (Vector m)) : Option ℕ := by
  classical
  let L := logicalPaulis BX CX BZ CZ
  exact if h : L.Nonempty then some ((L.image weight).min' (h.image weight)) else none

/-- Empty logical spaces have no finite distance; a nonempty component dominates an empty one. -/
def minDistance : Option ℕ → Option ℕ → Option ℕ
  | none, d => d
  | d, none => d
  | some a, some b => some (min a b)

end M6.CSS

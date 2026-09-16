import M6Character
import M6Pinned

open scoped BigOperators
namespace M6.Character
noncomputable def boundaryFactor {m : ℕ} (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2) : Polynomial ℤ := by
  classical
  exact if P i = none ∨ P i = some s then Polynomial.X ^ s.val else 0

noncomputable def pinnedCharacterFactor {m : ℕ} (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2) : Polynomial ℤ :=
  ∑ t : ZMod 2, Polynomial.C (sign (s*t)) * boundaryFactor P i t

noncomputable def pinnedTransform {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) (P : M6.Pinned.Pins m) : Polynomial ℤ :=
  ∑ q ∈ subspaceWords D, ∏ i, pinnedCharacterFactor P i (q i)

noncomputable def pinnedMonomial {m : ℕ} (P : M6.Pinned.Pins m) (v : Vector m) : Polynomial ℤ := by
  classical
  exact if M6.Pinned.agrees P v then Polynomial.X ^ M6.Pinned.weight v else 0
end M6.Character

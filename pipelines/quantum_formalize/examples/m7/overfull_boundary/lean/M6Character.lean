import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

open scoped BigOperators
namespace M6.Character
abbrev Vector (m : ℕ) := Fin m → ZMod 2

def dot {m : ℕ} (q z : Vector m) : ZMod 2 := ∑ i, q i * z i

def sign (s : ZMod 2) : ℤ := (-1) ^ s.val

def character {m : ℕ} (q z : Vector m) : ℤ := sign (dot q z)

noncomputable def subspaceWords {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) : Finset (Vector m) := by
  classical
  exact Finset.univ.filter (fun q => q ∈ D)

def Orthogonal {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) (z : Vector m) : Prop :=
  ∀ q ∈ D, dot q z = 0

noncomputable def dualWords {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) : Finset (Vector m) := by
  classical
  exact Finset.univ.filter (Orthogonal D)

noncomputable def orthogonalIndicator {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) (z : Vector m) : ℤ := by
  classical
  exact if Orthogonal D z then (subspaceWords D).card else 0

noncomputable def characterSum {m : ℕ} (D : Submodule (ZMod 2) (Vector m)) (z : Vector m) : ℤ :=
  ∑ q ∈ subspaceWords D, character q z

noncomputable def localTransform {m : ℕ} (w : Fin m → ZMod 2 → Polynomial ℤ) (q : Vector m) : Polynomial ℤ :=
  ∏ i, ∑ s : ZMod 2, Polynomial.C (sign (q i * s)) * w i s

noncomputable def weightedDual {m : ℕ} (D : Submodule (ZMod 2) (Vector m))
    (w : Fin m → ZMod 2 → Polynomial ℤ) : Polynomial ℤ :=
  ∑ z ∈ dualWords D, ∏ i, w i (z i)

noncomputable def weightedTransform {m : ℕ} (D : Submodule (ZMod 2) (Vector m))
    (w : Fin m → ZMod 2 → Polynomial ℤ) : Polynomial ℤ :=
  ∑ q ∈ subspaceWords D, localTransform w q
end M6.Character

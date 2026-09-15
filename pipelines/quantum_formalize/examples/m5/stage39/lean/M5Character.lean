import M5Foundation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
namespace M5.Character
abbrev BinaryVector (D : ℕ) := Fin D → ZMod 2

def bitSign (a b : ZMod 2) : ℤ := (-1) ^ (a * b).val

def value {D : ℕ} (lam z : BinaryVector D) : ℤ := ∏ i, bitSign (lam i) (z i)
end M5.Character

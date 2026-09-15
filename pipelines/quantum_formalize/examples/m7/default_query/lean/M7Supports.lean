import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
open scoped BigOperators
namespace M7.Supports
abbrev BP := Polynomial (ZMod 2)
abbrev Support (N : ℕ) := Finset (ZMod N)
noncomputable def indicator {N : ℕ} (A : Support N) (i : ZMod N) : ZMod 2 := if i ∈ A then 1 else 0
noncomputable def polynomial {N : ℕ} (A : Support N) : BP := ∑ i ∈ A, Polynomial.X ^ i.val
noncomputable def natSupport {N : ℕ} (A : Support N) : Finset ℕ := A.image ZMod.val
end M7.Supports

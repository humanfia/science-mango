import Mathlib.Data.Finset.Max
import Mathlib.Tactic
namespace M5.BirthSearch
def candidates (T lower B : ℕ) (C : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (B + 1)).filter (fun N => lower ≤ N ∧ T ∣ N ∧ 0 < C N)
def birth (T lower B : ℕ) (C : ℕ → ℤ) : Option ℕ :=
  if h : (candidates T lower B C).Nonempty then some ((candidates T lower B C).min' h)
  else none
end M5.BirthSearch

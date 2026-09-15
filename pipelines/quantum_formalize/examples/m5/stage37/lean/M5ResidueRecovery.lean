import Mathlib.Data.List.Basic
import Mathlib.Tactic
open scoped BigOperators
namespace M5.ResidueRecovery
def pick {T : ℕ} (f : Fin T → ℤ) : List (Fin T) → Option (Fin T) × ℕ
  | [] => (none, 0)
  | a :: xs => if 0 < f a then (some a, 1)
      else let rest := pick f xs; (rest.1, rest.2 + 1)
def recover {T : ℕ} (c : List (Fin T) → ℤ) (p : List (Fin T)) : ℕ → Option (List (Fin T)) × ℕ
  | 0 => (some p, 0)
  | n + 1 =>
      let chosen := pick (fun a => c (p ++ [a])) (List.finRange T)
      match chosen.1 with
      | none => (none, chosen.2)
      | some a => let result := recover c (p ++ [a]) n
                  (result.1, chosen.2 + result.2)
end M5.ResidueRecovery

import Mathlib.Data.List.Basic
import Mathlib.Tactic
namespace M5.BinaryRecovery
def recover (c : List Bool → ℤ) (p : List Bool) : ℕ → List Bool
  | 0 => p
  | n + 1 => if 0 < c (p ++ [false]) then recover c (p ++ [false]) n
      else recover c (p ++ [true]) n
end M5.BinaryRecovery

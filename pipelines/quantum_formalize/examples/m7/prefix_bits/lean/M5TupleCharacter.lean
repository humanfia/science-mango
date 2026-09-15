import M5Accepted
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace M5.TupleCharacter

def vectorSum {D n k : ℕ} (f : Fin n → M5.Character.BinaryVector D)
    (t : Fin k → Fin n) : M5.Character.BinaryVector D :=
  ∑ i : Fin k, f (t i)

def count {D n : ℕ} (k : ℕ) (f : Fin n → M5.Character.BinaryVector D)
    (z : M5.Character.BinaryVector D) : ℕ :=
  (Finset.univ.filter (fun t : Fin k → Fin n => vectorSum f t = z)).card

end M5.TupleCharacter

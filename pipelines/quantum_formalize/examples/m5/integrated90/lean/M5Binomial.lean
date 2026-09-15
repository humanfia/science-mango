import M5Foundation
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators
namespace M5.Binomial

def negativeCount (S : Finset ℕ) (f : ℕ → ℤ) : ℕ := (S.filter (fun s => f s = -1)).card

noncomputable def signedProduct (S : Finset ℕ) (f : ℕ → ℤ) : Polynomial ℤ :=
  ∏ s ∈ S, (1 + Polynomial.C (f s) * Polynomial.X)
end M5.Binomial

import M5Accepted
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
namespace M5.SubsetCharacter

def vectorSum {D : ℕ} (U : Finset ℕ) (f : ℕ → M5.Character.BinaryVector D) :
    M5.Character.BinaryVector D := ∑ s ∈ U, f s

noncomputable def signedProduct (S : Finset ℕ) (f : ℕ → ℤ) : Polynomial ℤ :=
  ∏ s ∈ S, (1 + Polynomial.C (f s) * Polynomial.X)

def count {D : ℕ} (S : Finset ℕ) (k : ℕ) (f : ℕ → M5.Character.BinaryVector D)
    (z : M5.Character.BinaryVector D) : ℕ :=
  ((S.powersetCard k).filter (fun U => vectorSum U f = z)).card

end M5.SubsetCharacter

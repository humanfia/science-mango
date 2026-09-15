import M5Foundation
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
namespace M5.FiniteExclusion
noncomputable def exclusionSum (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool) : ℤ :=
  ∑ H ∈ S.powerset, (-1 : ℤ)^H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)
end M5.FiniteExclusion

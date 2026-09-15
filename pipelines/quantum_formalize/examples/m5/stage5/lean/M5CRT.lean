import M5Foundation
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace M5.CRT

def repairResidue (e p : ℕ) : ℕ := if p ∣ e then 1 else 0

def primeProduct (δ : ℕ) : ℕ := ∏ p ∈ δ.primeFactors, p

end M5.CRT

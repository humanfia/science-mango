import M5Foundation
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped BigOperators
namespace M5.Connectivity

def supportGcd (N : ℕ) (A B : Finset ℕ) : ℕ := Nat.gcd N (Nat.gcd (A.gcd id) (B.gcd id))
end M5.Connectivity

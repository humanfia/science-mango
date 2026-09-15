import M5QuotientMonomialPeriod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace M5.RepairSupport

def repaired (A : Finset ℕ) (e q : ℕ) : Finset ℕ :=
  insert q (A.erase e)

def combinedGcd (A B : Finset ℕ) : ℕ :=
  Nat.gcd (A.gcd id) (B.gcd id)

end M5.RepairSupport

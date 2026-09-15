import Mathlib
namespace M7.FactorReplay
noncomputable section
abbrev BP := Polynomial (ZMod 2)
/-- Enumerate actual finite coefficient vectors, then build their polynomial. -/
def pool (n : ℕ) : Finset BP :=
  Finset.univ.image (fun a : Fin (n+1) → ZMod 2 => Polynomial.ofFn (n+1) a)
/-- The test only quantifies over an explicitly enumerated finite coefficient pool. -/
def irreducibleCheck (p : BP) : Bool :=
  decide p.Monic && decide (p ≠ 1) &&
    (pool (p.natDegree/2)).toList.all (fun q =>
      !(decide (q.Monic ∧ 0 < q.natDegree ∧ q.natDegree ≤ p.natDegree/2 ∧ p % q = 0)))
def product (factors : List (BP × ℕ)) : BP := (factors.map (fun t => t.1^t.2)).prod
def check (F : BP) (factors : List (BP × ℕ)) : Bool :=
  decide ((factors.map Prod.fst).Nodup) &&
  factors.all (fun t => irreducibleCheck t.1 && decide (0 < t.2)) &&
  decide (product factors = F)
/-- Retain the exact multiset multiplicity while storing each normalized factor once. -/
def expected (F : BP) : List (BP × ℕ) :=
  let fs := UniqueFactorizationMonoid.normalizedFactors F
  fs.toFinset.toList.map (fun p => (p,fs.count p))
end
end M7.FactorReplay

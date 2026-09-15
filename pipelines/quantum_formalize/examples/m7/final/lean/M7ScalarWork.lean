import M7ArithmeticLoopsAccepted
import M7ActualFactorizedAccepted

namespace M7.ScalarWork
open scoped BigOperators
/-- Unit-cost signed scalar arithmetic after coordinate and binomial preprocessing.
    Four operations per binary character coordinate, plus scalar setup. -/
def character (D : ℕ) : ℕ := 1 + 4*D
/-- Each negativeCount scans W and evaluates its character and sign test. -/
def negative (D : ℕ) (W : Finset ℕ) : ℕ := W.card * (2 + character D)
/-- Direct evaluation of the existing j-sum, including both occurrences of negativeCount.
    No constant-subexpression caching or bit-complexity improvement is assumed. -/
def term (D : ℕ) (W : Finset ℕ) (k : ℕ) : ℕ :=
  character D + ∑ _j ∈ Finset.range (k+1), (8 + 2 * negative D W)
/-- The existing guarded divisor/exclusion/character loops with per-term scalar charges.
    Polynomial factorization, coordinate preprocessing, binomials and integer bit costs
    remain explicit additional finite costs, as in original M7 section 11. -/
noncomputable def prefixWork (N w : ℕ) (F : M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℕ := by
  classical
  exact if A.card ≤ w ∧ B.card ≤ w then
    ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
      ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (16 + 2^(F * (∏ p ∈ S, p)).natDegree *
          (term (F * (∏ p ∈ S, p)).natDegree (M5.ConditionalCount.restricted WA d) (w-A.card) +
           term (F * (∏ p ∈ S, p)).natDegree (M5.ConditionalCount.restricted WB d) (w-B.card)))
    else 0
noncomputable def sector (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℕ := ∑ F ∈ E, prefixWork N w F A B WA WB
/-- Coordinate-position visits in the two independent full single-block mask scans. -/
noncomputable def maskPositions (N : ℕ) [NeZero N] : ℕ :=
  ∑ _u : M7.ActualFactorized.Outer N, ((∑ _s : ZMod N, N) + (∑ _t : ZMod N, N))
end M7.ScalarWork

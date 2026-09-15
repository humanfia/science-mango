import M5OrderCountAcceptedDependencies

namespace M5.OrderCount

noncomputable def nOne (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ) : ℤ := by
  classical
  exact if hP : P.Monic then M5.ArithmeticSubset.n P hP W k 1 else 0

def positivePositions (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun s => 0 < s)

def divisorPositions (N d : ℕ) : Finset ℕ :=
  (positivePositions N).filter (fun s => d ∣ s)

noncomputable def twoBlockIndicatorSum (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ) : ℤ := by
  classical
  exact ∑ U ∈ W.powersetCard k, ∑ V ∈ W.powersetCard k,
    if P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ∧ P ∣ M5.SupportPolynomial.ofSupport (insert 0 V) then 1 else 0

noncomputable def rawC (N w : ℕ) (F : M5.BinaryPolynomial) : ℤ := by
  classical
  exact ∑ d ∈ N.divisors, ArithmeticFunction.moebius d *
    ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
      (-1 : ℤ)^S.card * nOne (F * (∏ p ∈ S, p)) (divisorPositions N d) (w-1)^2

noncomputable def C (N w : ℕ) (F : M5.BinaryPolynomial) : ℤ := by
  classical
  exact if F ∣ M5.cyclicModulus N ∧ w ≤ N then rawC N w F else 0

noncomputable def pairIndicator (N : ℕ) (F : M5.BinaryPolynomial) (U V : Finset ℕ) : ℤ := by
  classical
  exact (∑ d ∈ N.divisors,
    if (∀ s ∈ insert 0 U, d ∣ s) ∧ (∀ s ∈ insert 0 V, d ∣ s)
    then ArithmeticFunction.moebius d else 0) *
    M5.PolynomialIndicator.factorExclusionSum
      (M5.SupportPolynomial.ofSupport (insert 0 U))
      (M5.SupportPolynomial.ofSupport (insert 0 V)) F N

noncomputable def validPairs (N w : ℕ) (F : M5.BinaryPolynomial) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (((positivePositions N).powersetCard (w-1)).product
    ((positivePositions N).powersetCard (w-1))).filter (fun pair =>
      M5.Connectivity.supportGcd N (insert 0 pair.1) (insert 0 pair.2) = 1 ∧
      M5.completeSignature (M5.SupportPolynomial.ofSupport (insert 0 pair.1))
        (M5.SupportPolynomial.ofSupport (insert 0 pair.2)) N = F)

end M5.OrderCount

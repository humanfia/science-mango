import M5OrderCountAcceptedDependencies
import M5CompletionBlockAccepted

namespace M5.ConditionalCount

def restricted (W : Finset ℕ) (d : ℕ) : Finset ℕ := W.filter (fun s => d ∣ s)

noncomputable def nSelected (P : M5.BinaryPolynomial) (A W : Finset ℕ) (k : ℕ) : ℤ := by
  classical
  exact if hP : P.Monic then M5.ArithmeticSubset.n P hP W k
    (AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A)) else 0

noncomputable def twoBlockIndicatorSum (P : M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) (kA kB : ℕ) : ℤ := by
  classical
  exact ∑ U ∈ WA.powersetCard kA, ∑ V ∈ WB.powersetCard kB,
    if P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ∧
      P ∣ M5.SupportPolynomial.ofSupport (B ∪ V) then 1 else 0

noncomputable def rawCompletion (N w : ℕ) (F : M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℤ := by
  classical
  exact ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
    ArithmeticFunction.moebius d *
      ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
        (-1 : ℤ)^S.card *
          nSelected (F * (∏ p ∈ S, p)) A (restricted WA d) (w-A.card) *
          nSelected (F * (∏ p ∈ S, p)) B (restricted WB d) (w-B.card)

noncomputable def completionC (N w : ℕ) (F : M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℤ :=
  if A.card ≤ w ∧ B.card ≤ w then rawCompletion N w F A B WA WB else 0

def PrefixOK (N w : ℕ) (A B WA WB : Finset ℕ) : Prop :=
  0 ∈ A ∧ 0 ∈ B ∧ A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧
  WA ⊆ Finset.range N ∧ WB ⊆ Finset.range N ∧
  Disjoint A WA ∧ Disjoint B WB ∧ A.card ≤ w ∧ B.card ≤ w

noncomputable def selectedDivisorSum (N : ℕ) (A B U V : Finset ℕ) : ℤ := by
  classical
  exact ∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
    if (∀ s ∈ U, d ∣ s) ∧ (∀ s ∈ V, d ∣ s) then ArithmeticFunction.moebius d else 0

noncomputable def pairIndicator (N : ℕ) (F : M5.BinaryPolynomial)
    (A B U V : Finset ℕ) : ℤ := by
  classical
  exact (∑ d ∈ (M5.Connectivity.supportGcd N A B).divisors,
    if (∀ s ∈ U, d ∣ s) ∧ (∀ s ∈ V, d ∣ s) then ArithmeticFunction.moebius d else 0) *
    M5.PolynomialIndicator.factorExclusionSum
      (M5.SupportPolynomial.ofSupport (A ∪ U)) (M5.SupportPolynomial.ofSupport (B ∪ V)) F N

noncomputable def validCompletions (N w : ℕ) (F : M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact ((WA.powersetCard (w-A.card)).product (WB.powersetCard (w-B.card))).filter (fun pair =>
    (A ∪ pair.1).card = w ∧ (B ∪ pair.2).card = w ∧
    M5.Connectivity.supportGcd N (A ∪ pair.1) (B ∪ pair.2) = 1 ∧
    M5.completeSignature (M5.SupportPolynomial.ofSupport (A ∪ pair.1))
      (M5.SupportPolynomial.ofSupport (B ∪ pair.2)) N = F)

end M5.ConditionalCount

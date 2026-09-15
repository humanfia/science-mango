import M5PolynomialIndicatorAccepted
import M5AnchoredTupleCountAccepted

open scoped BigOperators
namespace M5.ResidueCount

noncomputable def ROne (P : M5.BinaryPolynomial) (T d k : ℕ) : ℤ := by
  classical
  exact if hP : P.Monic then M5.ArithmeticTuple.R P hP T d k 1 else 0

noncomputable def tailPolynomial {T k : ℕ} (t : Fin k → Fin T) : M5.BinaryPolynomial :=
  1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (t i).val

def residueSupport {T k : ℕ} (t : Fin k → Fin T) : Finset ℕ :=
  insert 0 (Finset.univ.image (fun i : Fin k => (t i).val))

noncomputable def feasible {T k : ℕ} (F : M5.BinaryPolynomial)
    (a b : Fin k → Fin T) : Prop :=
  Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin k => (a i).val))
    (Finset.univ.gcd (fun i : Fin k => (b i).val))) = 1 ∧
  M5.completeSignature (tailPolynomial a) (tailPolynomial b) T = F

noncomputable def validTailPairs (T w : ℕ) (F : M5.BinaryPolynomial) :
    Finset ((Fin (w-1) → Fin T) × (Fin (w-1) → Fin T)) := by
  classical
  exact Finset.univ.filter (fun pair => feasible F pair.1 pair.2)

noncomputable def pairIndicator {T k : ℕ} (F : M5.BinaryPolynomial)
    (a b : Fin k → Fin T) : ℤ := by
  classical
  exact (∑ d ∈ T.divisors,
    if (∀ i : Fin k, d ∣ (a i).val) ∧ (∀ i : Fin k, d ∣ (b i).val)
    then ArithmeticFunction.moebius d else 0) *
    M5.PolynomialIndicator.factorExclusionSum (tailPolynomial a) (tailPolynomial b) F T

noncomputable def rawA (T w : ℕ) (F : M5.BinaryPolynomial) : ℤ := by
  classical
  exact ∑ d ∈ T.divisors, ArithmeticFunction.moebius d *
    ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset,
      (-1 : ℤ)^S.card * ROne (F * (∏ p ∈ S, p)) T d (w-1)^2

noncomputable def A (w : ℕ) (F : M5.BinaryPolynomial) : ℤ :=
  rawA (M5.signaturePeriod F) w F

end M5.ResidueCount

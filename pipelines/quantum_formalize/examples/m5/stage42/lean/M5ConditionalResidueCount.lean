import M5ResidueCountAccepted
import M5TupleCompletionAccepted
import Mathlib.Algebra.BigOperators.Group.List.Basic

open scoped BigOperators
namespace M5.ConditionalResidueCount

noncomputable def selectedPolynomial {T : ℕ} (p : List (Fin T)) : M5.BinaryPolynomial :=
  1 + (p.map (fun r => (Polynomial.X : M5.BinaryPolynomial) ^ r.val)).sum

def prefixGcd {T : ℕ} (p : List (Fin T)) : ℕ :=
  (p.map (fun r => r.val)).foldr Nat.gcd 0

def selectedGcd (T : ℕ) (p q : List (Fin T)) : ℕ :=
  Nat.gcd T (Nat.gcd (prefixGcd p) (prefixGcd q))

def remaining {T : ℕ} (w : ℕ) (p : List (Fin T)) : ℕ := w - 1 - p.length

def fits {T : ℕ} (w : ℕ) (p q : List (Fin T)) : Prop :=
  p.length ≤ w - 1 ∧ q.length ≤ w - 1

noncomputable def RSelected (P Z : M5.BinaryPolynomial) (T d k : ℕ) : ℤ := by
  classical
  exact if hP : P.Monic then M5.ArithmeticTuple.R P hP T d k (AdjoinRoot.mk P Z) else 0

noncomputable def completedPolynomial {T k : ℕ} (Z : M5.BinaryPolynomial)
    (a : Fin k → Fin T) : M5.BinaryPolynomial :=
  Z + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (a i).val

noncomputable def divisibilityIndicator (P ZA ZB : M5.BinaryPolynomial)
    {T k l : ℕ} (d : ℕ) (a : Fin k → Fin T) (b : Fin l → Fin T) : ℤ := by
  classical
  exact if ((∀ i : Fin k, d ∣ (a i).val) ∧ P ∣ completedPolynomial ZA a) ∧
    ((∀ i : Fin l, d ∣ (b i).val) ∧ P ∣ completedPolynomial ZB b) then 1 else 0

noncomputable def feasible {T : ℕ} (w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) (a : Fin (remaining w p) → Fin T)
    (b : Fin (remaining w q) → Fin T) : Prop :=
  Nat.gcd (selectedGcd T p q) (Nat.gcd
    (Finset.univ.gcd (fun i : Fin (remaining w p) => (a i).val))
    (Finset.univ.gcd (fun i : Fin (remaining w q) => (b i).val))) = 1 ∧
  M5.completeSignature (completedPolynomial (selectedPolynomial p) a)
    (completedPolynomial (selectedPolynomial q) b) T = F

noncomputable def feasibleIndicator {T : ℕ} (w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) (a : Fin (remaining w p) → Fin T)
    (b : Fin (remaining w q) → Fin T) : ℤ := by
  classical
  exact if feasible w F p q a b then 1 else 0

noncomputable def pairIndicator {T : ℕ} (w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) (a : Fin (remaining w p) → Fin T)
    (b : Fin (remaining w q) → Fin T) : ℤ := by
  classical
  exact (∑ d ∈ (selectedGcd T p q).divisors,
    if (∀ i : Fin (remaining w p), d ∣ (a i).val) ∧
      (∀ i : Fin (remaining w q), d ∣ (b i).val)
    then ArithmeticFunction.moebius d else 0) *
    M5.PolynomialIndicator.factorExclusionSum
      (completedPolynomial (selectedPolynomial p) a)
      (completedPolynomial (selectedPolynomial q) b) F T

noncomputable def rawConditionalA (T w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) : ℤ := by
  classical
  exact ∑ d ∈ (selectedGcd T p q).divisors, ArithmeticFunction.moebius d *
    ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus T) F).powerset,
      (-1 : ℤ)^S.card *
      (RSelected (F * (∏ f ∈ S, f)) (selectedPolynomial p) T d (remaining w p) *
      RSelected (F * (∏ f ∈ S, f)) (selectedPolynomial q) T d (remaining w q))

noncomputable def conditionalAAt (T w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) : ℤ := by
  classical
  exact if fits w p q then rawConditionalA T w F p q else 0

noncomputable def validCompletions (T w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin T)) :
    Finset ((Fin (remaining w p) → Fin T) × (Fin (remaining w q) → Fin T)) := by
  classical
  exact if fits w p q then Finset.univ.filter (fun ab => feasible w F p q ab.1 ab.2)
    else ∅

noncomputable def conditionalA (w : ℕ) (F : M5.BinaryPolynomial)
    (p q : List (Fin (M5.signaturePeriod F))) : ℤ :=
  conditionalAAt (M5.signaturePeriod F) w F p q

end M5.ConditionalResidueCount

import M5ArithmeticTupleAccepted
open scoped BigOperators
namespace M5.AnchoredTupleCount
noncomputable def count (P : M5.BinaryPolynomial) (T d k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin k → Fin (T / d) =>
    P ∣ 1 + M5.ArithmeticTuple.tuplePolynomial T d k t)).card
noncomputable def restrictedCount (P : M5.BinaryPolynomial) (T d k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin k → Fin T =>
    (∀ i : Fin k, d ∣ (t i).val) ∧
    P ∣ 1 + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (t i).val)).card
end M5.AnchoredTupleCount

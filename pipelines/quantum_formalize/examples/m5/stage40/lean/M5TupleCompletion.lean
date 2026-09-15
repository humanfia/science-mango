import M5AnchoredTupleCountAccepted
open scoped BigOperators
namespace M5.TupleCompletion
noncomputable def count (P Z : M5.BinaryPolynomial) (T d k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin k → Fin (T / d) =>
    P ∣ Z + M5.ArithmeticTuple.tuplePolynomial T d k t)).card
noncomputable def restrictedCount (P Z : M5.BinaryPolynomial) (T d k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin k → Fin T =>
    (∀ i : Fin k, d ∣ (t i).val) ∧
    P ∣ Z + ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (t i).val)).card
end M5.TupleCompletion

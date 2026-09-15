import M5Checkpoint90
open scoped BigOperators
namespace M5.ArithmeticTuple
noncomputable def tuplePolynomial (T d k : ℕ) (t : Fin k → Fin (T / d)) : M5.BinaryPolynomial :=
  ∑ i : Fin k, (Polynomial.X : M5.BinaryPolynomial) ^ (d * (t i).val)
noncomputable def numerator (P : M5.BinaryPolynomial) (hP : P.Monic)
    (T d k : ℕ) (z : AdjoinRoot P) : ℤ :=
  ∑ lam : M5.Character.BinaryVector P.natDegree,
    M5.QuotientCharacter.value P hP lam z *
      (∑ j : Fin (T / d), M5.QuotientCharacter.value P hP lam
        (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ (d * j.val)))) ^ k
noncomputable def R (P : M5.BinaryPolynomial) (hP : P.Monic)
    (T d k : ℕ) (z : AdjoinRoot P) : ℤ :=
  numerator P hP T d k z / (2 : ℤ) ^ P.natDegree
end M5.ArithmeticTuple

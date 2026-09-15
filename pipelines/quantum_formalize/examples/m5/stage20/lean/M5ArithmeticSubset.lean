import M5Checkpoint72
import M5SubsetCountAccepted

open scoped BigOperators
namespace M5.ArithmeticSubset

noncomputable def monomialValue (P : M5.BinaryPolynomial) (hP : P.Monic)
    (lam : M5.Character.BinaryVector P.natDegree) (s : ℕ) : ℤ :=
  M5.QuotientCharacter.value P hP lam
    (AdjoinRoot.mk P ((Polynomial.X : M5.BinaryPolynomial) ^ s))

noncomputable def negativeCount (P : M5.BinaryPolynomial) (hP : P.Monic)
    (W : Finset ℕ) (lam : M5.Character.BinaryVector P.natDegree) : ℕ :=
  M5.Binomial.negativeCount W (monomialValue P hP lam)

noncomputable def binomialTerm (P : M5.BinaryPolynomial) (hP : P.Monic)
    (W : Finset ℕ) (k : ℕ) (lam : M5.Character.BinaryVector P.natDegree) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j *
    ((negativeCount P hP W lam).choose j : ℤ) *
    ((W.card - negativeCount P hP W lam).choose (k - j) : ℤ)

noncomputable def numerator (P : M5.BinaryPolynomial) (hP : P.Monic)
    (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P) : ℤ :=
  ∑ lam : M5.Character.BinaryVector P.natDegree,
    M5.QuotientCharacter.value P hP lam z * binomialTerm P hP W k lam

noncomputable def n (P : M5.BinaryPolynomial) (hP : P.Monic)
    (W : Finset ℕ) (k : ℕ) (z : AdjoinRoot P) : ℤ :=
  numerator P hP W k z / (2 : ℤ) ^ P.natDegree

end M5.ArithmeticSubset

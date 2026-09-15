import M5PackingInjective
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Degree.Support

open scoped BigOperators
namespace M5.SupportPolynomial

noncomputable def ofSupport (S : Finset ℕ) : M5.BinaryPolynomial :=
  ∑ e ∈ S, (Polynomial.X : M5.BinaryPolynomial) ^ e

noncomputable def ofResidueTuple {w T : ℕ} (r : Fin w → Fin T) : M5.BinaryPolynomial :=
  ∑ i : Fin w, (Polynomial.X : M5.BinaryPolynomial) ^ (r i).val

end M5.SupportPolynomial

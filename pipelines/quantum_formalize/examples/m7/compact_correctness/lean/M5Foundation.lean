import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Shared vocabulary for an initial M5 auxiliary-lemma experiment.
Source: period_residue_arithmetic_law_reviewed/PROOF.md, sections 1 and 5.
This module contains definitions only. It does not state that the complete M5
arithmetic counting or birth theorem has been formalized.
-/

namespace M5

abbrev BinaryPolynomial := Polynomial (ZMod 2)

noncomputable def cyclicModulus (N : ℕ) : BinaryPolynomial := Polynomial.X ^ N + 1

noncomputable def completeSignature (a b : BinaryPolynomial) (N : ℕ) :
    BinaryPolynomial := EuclideanDomain.gcd (EuclideanDomain.gcd a b) (cyclicModulus N)

def packedExponent (T r j : ℕ) : ℕ := r + j * T

def packingCutoff (w T : ℕ) : ℕ := w * T * (T + 2)

def birthBound (w T : ℕ) : ℕ := packingCutoff w T + 2 ^ (w * T)

end M5

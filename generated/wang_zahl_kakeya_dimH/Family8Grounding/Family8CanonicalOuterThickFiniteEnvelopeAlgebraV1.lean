import Mathlib.Tactic

/-!
# Finite outer/thick envelope algebra

Pure monotonicity that replaces both the literal conflict loss and the
selected-witness cardinality by one common finite envelope.
-/

open scoped ENNReal

namespace Family8CanonicalOuterThickFiniteEnvelopeAlgebraV1

set_option autoImplicit false
set_option warningAsError true

theorem outerThickFiniteEnvelope_mono
    (N loss C W : ENNReal) (beta : Real) (hbeta : 0 ≤ beta)
    (hloss : loss ≤ N) (hW : W ≤ N) :
    (((N * loss) * N) *
      (max 1 ((216 : ENNReal) * C * W)) ^ (beta / 2)) ≤
      (((N * N) * N) *
        (max 1 ((216 : ENNReal) * C * N)) ^ (beta / 2)) := by
  apply mul_le_mul'
  · exact mul_le_mul' (mul_le_mul' le_rfl hloss) le_rfl
  · apply ENNReal.rpow_le_rpow
    · exact max_le_max le_rfl (mul_le_mul' le_rfl hW)
    · linarith

#print axioms outerThickFiniteEnvelope_mono

end Family8CanonicalOuterThickFiniteEnvelopeAlgebraV1

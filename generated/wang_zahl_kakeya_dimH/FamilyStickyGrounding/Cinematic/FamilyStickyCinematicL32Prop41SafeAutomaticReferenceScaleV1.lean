import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41SafeAutomaticReferenceScaleV1

/-!
# A safe automatic reference scale

For any real margin, `1 + |margin|` is nonnegative and three times this
scale strictly dominates the original margin.  This elementary adapter lets
dependent actual packages choose their reference scale after the package has
fixed its trace shift.
-/

/-- A positive reference scale chosen after an arbitrary margin is known. -/
def prop41SafeAutomaticReferenceScale (margin : Real) : Real :=
  1 + |margin|

theorem prop41SafeAutomaticReferenceScale_nonneg (margin : Real) :
    0 <= prop41SafeAutomaticReferenceScale margin := by
  unfold prop41SafeAutomaticReferenceScale
  positivity

theorem lt_three_mul_prop41SafeAutomaticReferenceScale (margin : Real) :
    margin < 3 * prop41SafeAutomaticReferenceScale margin := by
  have hle : margin <= |margin| := le_abs_self margin
  have hnonneg : 0 <= |margin| := abs_nonneg margin
  unfold prop41SafeAutomaticReferenceScale
  linarith

#print axioms prop41SafeAutomaticReferenceScale_nonneg
#print axioms lt_three_mul_prop41SafeAutomaticReferenceScale

end FamilyStickyCinematicL32Prop41SafeAutomaticReferenceScaleV1
